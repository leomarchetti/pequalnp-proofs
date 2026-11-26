"""Harvester: watch other contributors' open reduction PRs and flag raceable children early.

usage: harvest_loop.py outdir [minutes_back]
Every 3 minutes, list open PRs (not ours) that add one R_*.lean file, created in the last
minutes_back minutes (default 90) and not REJECTED. For each new one, fetch the file at its head
commit, split the theorem's hypotheses, and save each as outdir/<gap>_<pr>_<i>.txt. Print one
CANDIDATE line per hypothesis that looks quick to prove:
  NOAND  - a no-AND-gate side of a Monotone2/IsAO2 circuit statement (OR-only argument)
  NOCIRC - no circuit quantifier at all (often finite and decidable)
Other hypotheses are saved and counted but not flagged.
"""
import json, os, re, subprocess, sys, time, datetime

out = sys.argv[1]
back = int(sys.argv[2]) if len(sys.argv) > 2 else 90
os.makedirs(out, exist_ok=True)
seen = set()

def gh(*a):
    return subprocess.run(['gh', *a], capture_output=True, text=True, encoding='utf-8').stdout

def hyps_of(raw):
    m = re.search(r'theorem PEqualNP\.Outside\.R_\w+', raw)
    if not m: return []
    i = m.end(); hs = []
    while True:
        j = i
        while j < len(raw) and raw[j] in ' \t\r\n': j += 1
        if j >= len(raw) or raw[j] != '(': break
        depth = 0; k = j
        while True:
            c = raw[k]; depth += (c == '(') - (c == ')'); k += 1
            if depth == 0: break
        nm, _, body = raw[j + 1:k - 1].partition(':')
        hs.append((nm.strip(), body.strip()))
        i = k
    return hs

print('harvester started', flush=True)
while True:
    try:
        since = (datetime.datetime.now(datetime.timezone.utc) - datetime.timedelta(minutes=back)).strftime('%Y-%m-%dT%H:%M:%SZ')
        prs = json.loads(gh('pr', 'list', '-R', 'open-goat/pequalnp-proofs', '--state', 'open', '--limit', '100',
                            '--search', 'created:>' + since,
                            '--json', 'number,author,files,comments,headRefOid,createdAt') or '[]')
        for p in prs:
            if p['number'] in seen or p['author']['login'] == 'leomarchetti' or not p['files']: continue
            path = p['files'][0]['path']
            if '/R_' not in path: seen.add(p['number']); continue
            if any('REJECTED' in c['body'] for c in p['comments']): seen.add(p['number']); continue
            raw = gh('api', f"repos/open-goat/pequalnp-proofs/contents/{path}?ref={p['headRefOid']}",
                     '-H', 'Accept: application/vnd.github.raw')
            hs = hyps_of(raw)
            if not hs: continue
            seen.add(p['number'])
            gap = re.search(r'R_meta_(\d+)_', path).group(1)
            acc = 'ACCEPTED' if any('ACCEPTED' in c['body'] for c in p['comments']) else 'pending'
            flagged = 0
            for idx, (nm, body) in enumerate(hs):
                fn = os.path.join(out, f"{gap}_{p['number']}_{idx}.txt")
                open(fn, 'w', encoding='utf-8', newline='\n').write(body)
                mark = ''
                if re.search(r'¬\s*\(?\s*∃[^,]*gates', body) and 'GateOp.and' in body and re.search(r'Monotone2|IsAO2', body):
                    mark = 'NOAND'
                elif 'Circuit' not in body:
                    mark = 'NOCIRC'
                if mark == 'NOCIRC':
                    lf = os.path.join(out, f"try_{gap}_{p['number']}_{idx}.lean")
                    NL = chr(10)
                    head = NL.join(['import PEqualNP.Defs', '', 'set_option maxRecDepth 100000 in',
                                    'set_option maxHeartbeats 4000000 in', 'theorem t :', '    '])
                    open(lf, 'w', encoding='utf-8', newline=NL).write(head + body + ' := by decide +kernel' + NL)
                    try:
                        r = subprocess.run(['lake', 'env', 'lean', os.path.abspath(lf)], cwd='lean', capture_output=True, text=True, timeout=150)
                        ok = r.returncode == 0 and 'error' not in r.stdout
                    except subprocess.TimeoutExpired:
                        ok = False
                    mark = 'AUTO-PROVED(decide)' if ok else ''
                if mark:
                    flagged += 1
                    print('CANDIDATE', mark, 'L-meta-' + gap, 'PR', p['number'], p['author']['login'], acc,
                          'hyp', nm, 'len', len(body), fn, flush=True)
            print('scanned PR', p['number'], 'L-meta-' + gap, len(hs), 'hyps,', flagged, 'flagged', flush=True)
    except Exception as e:
        print('harvest error', type(e).__name__, str(e)[:120], flush=True)
    time.sleep(180)
