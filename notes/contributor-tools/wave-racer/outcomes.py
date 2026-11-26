"""Read the live state of every racer PR in sent2.tsv straight from GitHub (GraphQL by PR number, 100 per query: no
search index lag) and write outcomes.tsv: step, pr, mode, lease_points, state, merged_at, verdict.
usage: python -I -X utf8 .pnp/race/outcomes.py   -> prints a summary by mode"""
import json, os, re, subprocess, collections
DIR = os.path.dirname(os.path.abspath(__file__))
rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(DIR, 'sent2.tsv'), encoding='utf-8')][1:]
out = {}
for i in range(0, len(rows), 100):
    chunk = rows[i:i + 100]
    q = 'query { repository(owner: "open-goat", name: "pequalnp-proofs") { ' + ' '.join(
        'p%s: pullRequest(number: %s) { state mergedAt comments(last: 3) { nodes { body } } }' % (r[2], r[2]) for r in chunk) + ' } }'
    res = subprocess.run(['gh', 'api', 'graphql', '-f', 'query=' + q], capture_output=True, text=True, encoding='utf-8')
    data = json.loads(res.stdout)['data']['repository']
    for r in chunk:
        p = data.get('p' + r[2]) or {}
        body = ' '.join(n['body'] for n in (p.get('comments') or {}).get('nodes', []))
        m = re.search(r'stood down|proved first|REJECTED|FAULT|ACCEPTED', body)
        out[r[2]] = (p.get('state'), p.get('mergedAt') or '', m.group(0) if m else '')
with open(os.path.join(DIR, 'outcomes.tsv'), 'w', encoding='utf-8') as f:
    f.write('step\tpr\tmode\tlease_points\tstate\tmerged_at\tverdict\n')
    for r in rows: f.write('\t'.join([r[1], r[2], r[3], r[4]] + list(out[r[2]])) + '\n')
c = collections.Counter((r[3], out[r[2]][0], out[r[2]][2]) for r in rows)
for mode in ('leaseless', 'lease'):
    sent = sum(v for k, v in c.items() if k[0] == mode)
    merged = [r for r in rows if r[3] == mode and out[r[2]][0] == 'MERGED']
    pts = sum(10 if mode == 'leaseless' else int(r[4] or 0) for r in merged)
    print('%-9s sent %4d | merged %3d (%d pts) | %s' % (mode, sent, len(merged), pts,
          ', '.join('%s %s=%d' % (k[1].lower(), k[2], v) for k, v in sorted(c.items()) if k[0] == mode and k[1] != 'OPEN') or 'nothing finished'))
    for r in merged: print('    merged', r[1], '#' + r[2], out[r[2]][1][11:19])

# Comparison per mode: points per hour = PRs created per hour x share merged x points per merge.
from datetime import datetime
print()
print('mode       PRs/hour  merged/sent  merged/finished  pts/merge  -> pts/hour (sent-based / finished-based)')
for mode in ('leaseless', 'lease'):
    R = [r for r in rows if r[3] == mode]
    if not R: continue
    t = sorted(datetime.fromisoformat(r[0]) for r in R)
    hours = max((t[-1] - t[0]).total_seconds() / 3600, 1 / 60)
    rate = min(len(R) / hours, 500)   # GitHub refused PR creation past about 500 an hour: no mode can sustain more
    merged = [r for r in R if out[r[2]][0] == 'MERGED']
    finished = [r for r in R if out[r[2]][0] != 'OPEN' and out[r[2]][2] != 'stood down']
    ppm = (sum(10 if mode == 'leaseless' else int(r[4] or 0) for r in merged) / len(merged)) if merged else \
          (10 if mode == 'leaseless' else sum(int(r[4] or 0) for r in R) / len(R))
    ms, mf = len(merged) / len(R), (len(merged) / len(finished) if finished else float('nan'))
    print('%-9s  %7.0f  %5.1f%% (%d)  %6.1f%% (%d/%d)  %8.1f   -> %.0f / %.0f' % (mode, rate, 100 * ms, len(merged), 100 * mf, len(merged),
          len(finished), ppm, rate * ms * ppm, rate * mf * ppm if finished else float('nan')))
print('(PRs/hour: over each mode\'s own sending window; finished excludes stood-down weight-1 steps;'
      ' pts/merge for lease uses lease prices until merges exist)')
