"""Bulk tactic triage: try short closing tactics on many gap statements with `lake env lean`.

usage: triage.py gaps.json ids.txt outdir results.jsonl [workers] [timeout_s]
Run from the repository root. Writes one scratch file per (gap, template) under outdir and
appends {"id", "tpl", "ok", "secs", "err"} lines to results.jsonl. A hit is only a candidate:
re-check with the desk skeleton and `tools/pnp.sh check` before submitting.
"""
import json, sys, os, subprocess, time, concurrent.futures as cf

TEMPLATES = {
    'dk': 'by decide +kernel',
    'simp': 'by simp',
    'nn': 'by norm_num',
}
OPTS = '\nset_option maxRecDepth 100000 in\nset_option maxHeartbeats 1000000 in\n'

def run(job):
    gid, tpl, path, timeout = job
    t0 = time.time()
    try:
        p = subprocess.run(['lake', 'env', 'lean', os.path.abspath(path)], cwd='lean',
                           capture_output=True, text=True, timeout=timeout)
        ok = p.returncode == 0 and 'error' not in p.stdout
        err = '' if ok else (p.stdout + p.stderr).strip().splitlines()[0][:200] if (p.stdout + p.stderr).strip() else 'rc=%d' % p.returncode
    except subprocess.TimeoutExpired:
        ok, err = False, 'timeout'
    return {'id': gid, 'tpl': tpl, 'ok': ok, 'secs': round(time.time() - t0, 1), 'err': err}

def main():
    gaps, ids, outdir, res = sys.argv[1:5]
    workers = int(sys.argv[5]) if len(sys.argv) > 5 else 6
    timeout = int(sys.argv[6]) if len(sys.argv) > 6 else 120
    G = {x['id']: x for x in json.load(open(gaps, encoding='utf-8'))['gaps']}
    os.makedirs(outdir, exist_ok=True)
    done = set()
    if os.path.exists(res):
        for line in open(res, encoding='utf-8'):
            r = json.loads(line); done.add((r['id'], r['tpl']))
    jobs = []
    # template-major order: the cheap whole-statement `decide +kernel` pass runs over every gap first
    for tpl, tac in TEMPLATES.items():
        for gid in [l.strip() for l in open(ids) if l.strip()]:
            st = G[gid]['statement'].strip()
            if (gid, tpl) in done: continue
            path = os.path.join(outdir, '%s_%s.lean' % (gid.replace('-', '_'), tpl))
            with open(path, 'w', encoding='utf-8', newline='\n') as f:
                imps = ''.join('import %s\n' % m for m in (G[gid].get('imports') or ['PEqualNP.Defs']))
                f.write(imps + OPTS + 'theorem triage_%s : %s := %s\n' % (gid.replace('-', '_'), st, tac))
            jobs.append((gid, tpl, path, timeout))
    with cf.ThreadPoolExecutor(workers) as ex, open(res, 'a', encoding='utf-8') as out:
        for r in ex.map(run, jobs):
            out.write(json.dumps(r) + '\n'); out.flush()
            if r['ok']:
                print('HIT', r['id'], r['tpl'], r['secs'], flush=True)

main()
