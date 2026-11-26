"""Watch the desk snapshot for posted reduction children and submit prepared proofs at once.

usage: auto_children.py targets.txt
targets.txt: one line per child: name h2path childpath helperNS
All children matched in one poll are prepared in parallel (lease, splice, check: fastprep.sh);
each is submitted as soon as its check passes, one at a time (fastsubmit.sh holds the git work).
No competitor check (owner's instruction): submit refuses by itself if the step is already proved.
The targets file is re-read every poll, so new children can be added while it runs.
"""
import json, re, sys, time, urllib.request, subprocess, threading

BASH = 'C:/Program Files/Git/bin/bash.exe'
git_lock = threading.Lock()

def norm(s):
    # canonicalise numeral type ascriptions: (13 : ℕ) -> 13, then (1 : Fin 13) -> 1
    s = re.sub(r'\((\d+) : ℕ\)', r'\1', s)
    s = re.sub(r'\((\d+) : Fin (\d+)\)', r'\1', s)
    s = re.sub(r'\bx\d+\b', 'X', s)
    s = re.sub(r'\bj\b', 'X', s)
    return re.sub(r'[\s()]', '', s)

def say(*a):
    print(*a, flush=True)

def handle(name, gid, child, ns):
    p = subprocess.run([BASH, '.pnp/scratch/fastprep.sh', gid, child, ns], capture_output=True, text=True)
    out = p.stdout + p.stderr
    for line in out.splitlines():
        if re.search(r'PREP_|racing|error', line):
            say('  ' + name + ' ' + line.strip())
    if 'PREP_OK' not in out:
        return
    with git_lock:
        q = subprocess.run([BASH, '.pnp/scratch/fastsubmit.sh', gid], capture_output=True, text=True)
        for line in (q.stdout + q.stderr).splitlines():
            if re.search(r'https|submitted|STOP|refused|proved|done', line):
                say('  ' + name + ' ' + line.strip())

def load(path, done):
    T = {}
    for line in open(path, encoding='utf-8'):
        p = line.split()
        if len(p) == 4 and p[0] not in done:
            T[p[0]] = (norm(open(p[1], encoding='utf-8').read().strip()), p[2], p[3])
    return T

done = set()
last = None
import os
DONE_FILE = '.pnp/tools/auto_done.txt'
if os.path.exists(DONE_FILE):
    for line in open(DONE_FILE, encoding='utf-8'):
        if line.split(): done.add(line.split()[0])
say('started; already handled:', len(done))
while True:
    try:
        targets = load(sys.argv[1], done)
        req = urllib.request.Request('https://data.pequalnp.com/data/desk/gaps.json',
                                     headers={'User-Agent': 'curl/8.0'})
        with urllib.request.urlopen(req, timeout=60) as r:
            D = json.load(r)
        if D.get('updated_at') != last:
            last = D.get('updated_at')
            hits = []
            for g in D['gaps']:
                st = g.get('statement')
                if not st: continue
                n = norm(st)
                for name, (t, child, ns) in targets.items():
                    if n == t and name not in done:
                        done.add(name)
                        # persist, so a restarted instance never re-handles this child
                        with open(DONE_FILE, 'a', encoding='utf-8') as fd:
                            fd.write(name + ' ' + g['id'] + '\n')
                        hits.append((name, g['id'], child, ns, g.get('pr_open')))
            for name, gid, child, ns, pr in hits:
                say('POSTED', name, gid, 'pr_open=%s' % pr, last)
            th = [threading.Thread(target=handle, args=(n_, g_, c_, s_)) for n_, g_, c_, s_, _ in hits]
            for t in th: t.start()
            for t in th: t.join()
    except Exception as e:
        say('poll error', type(e).__name__, getattr(e, 'code', ''))
    time.sleep(10)
