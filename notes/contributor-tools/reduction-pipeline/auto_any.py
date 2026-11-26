"""Race ANY newly posted step whose shape fits a generic template (T1 no-AND, T2 small size,
T3 output-is-input), not only children we prepared in advance.

usage: auto_any.py targets.txt
Every 10 s, when the desk snapshot changes: for each step id not seen before (persisted in
.pnp/tools/any_seen.txt), skip it if it has an open PR or matches a prepared target; otherwise run
.pnp/gen/gen_generic.py. Each candidate proof is checked LOCALLY with `lake env lean` first (in
parallel); only a step with a passing candidate is leased (--proof-of, which is then true),
spliced, checked by tools/pnp.sh and submitted (fastprep.sh / fastsubmit.sh, which holds a git lock).
"""
import json, os, re, sys, time, subprocess, threading, urllib.request
from concurrent.futures import ThreadPoolExecutor

BASH = 'C:/Program Files/Git/bin/bash.exe'
SEEN = '.pnp/tools/any_seen.txt'
WORK = '.pnp/gen/live'
os.makedirs(WORK, exist_ok=True)

def norm(s):
    s = re.sub(r'\bx\d+\b', 'X', s); s = re.sub(r'\bj\b', 'X', s)
    return re.sub(r'[\s()]', '', s)

def say(*a): print(time.strftime('%H:%M:%S'), *a, flush=True)

seen = set()
if os.path.exists(SEEN):
    seen = set(open(SEEN, encoding='utf-8').read().split())

def targets():
    T = set()
    for line in open(sys.argv[1], encoding='utf-8'):
        p = line.split()
        if len(p) == 4 and os.path.exists(p[1]):
            T.add(norm(open(p[1], encoding='utf-8').read().strip()))
    return T

def check(fn):
    r = subprocess.run(['lake', 'env', 'lean', os.path.abspath(fn)], cwd='lean', capture_output=True, text=True)
    return r.returncode == 0 and 'error' not in r.stdout

def handle(gid, st):
    tag = gid.replace('-', '_')
    sf = os.path.join(WORK, tag + '.txt')
    open(sf, 'w', encoding='utf-8', newline='\n').write(st)
    g = subprocess.run(['python', '-I', '-X', 'utf8', '.pnp/gen/gen_generic.py', sf, WORK, tag],
                       capture_output=True, text=True)
    files = g.stdout.split()
    if not files: return
    say('CANDIDATES', gid, ' '.join(os.path.basename(f) for f in files))
    with ThreadPoolExecutor(len(files)) as ex:
        res = list(ex.map(check, files))
    good = [f for f, ok in zip(files, res) if ok]
    if not good:
        say('NO-PROOF', gid); return
    say('PROVED-LOCALLY', gid, os.path.basename(good[0]))
    p = subprocess.run([BASH, '.pnp/scratch/fastprep.sh', gid, good[0], 'PEqualNP.Outside.GenKit'],
                       capture_output=True, text=True)
    out = p.stdout + p.stderr
    for line in out.splitlines():
        if re.search(r'PREP_|racing', line): say('  ' + gid + ' ' + line.strip())
    if 'PREP_OK' not in out: return
    q = subprocess.run([BASH, '.pnp/scratch/fastsubmit.sh', gid], capture_output=True, text=True)
    for line in (q.stdout + q.stderr).splitlines():
        if re.search(r'https|submitted|STOP|refused|proved|LOCK', line): say('  ' + gid + ' ' + line.strip())

last = None
say('started; seen', len(seen))
first = not seen
while True:
    try:
        req = urllib.request.Request('https://data.pequalnp.com/data/desk/gaps.json', headers={'User-Agent': 'curl/8.0'})
        with urllib.request.urlopen(req, timeout=60) as r:
            D = json.load(r)
        if D.get('updated_at') != last:
            last = D.get('updated_at')
            T = targets()
            new = []
            for g in D['gaps']:
                gid = g['id']
                if gid in seen: continue
                seen.add(gid)
                with open(SEEN, 'a', encoding='utf-8') as fd: fd.write(gid + '\n')
                st = (g.get('statement') or '').strip()
                if first or g.get('pr_open') or not st: continue          # first pass: only record
                if norm(st) in T: continue                               # prepared child: auto_children handles it
                if 'PEqualNP.CircuitLowerBounds.Circuit' not in st[:80]: continue   # generator decides the rest
                new.append((gid, st))
            if first:
                say('baseline recorded:', len(seen)); first = False
            th = [threading.Thread(target=handle, args=a) for a in new]
            for t in th: t.start()
            for t in th: t.join()
    except Exception as e:
        say('poll error', type(e).__name__, str(e)[:100])
    time.sleep(10)
