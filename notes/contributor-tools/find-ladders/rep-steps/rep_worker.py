"""Persistent worker for the desk's small 'Represents' FIND steps.

Statement shape (k by k bipartite graph, one vertex a side, AND/OR/NOT circuit of at most s gates):
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ Represents (fun u v : Fin k => (MASK : ℕ).testBit (k * u.val + v.val)) C
Loop (every 30 s): new matching steps -> SAT (synth_sat3.py in WSL, NOT allowed) -> local Lean check of
our file -> lease with --proof-of (only after the local check passed) -> splice into the desk
skeleton -> tools/pnp.sh check -> fastsubmit.sh (git lock). A step another agent holds is retried
after its head start ends. State in .pnp/rep44/worker_state.json, log in .pnp/rep44/worker.log.
usage: python -I -X utf8 -u .pnp/rep44/rep_worker.py
"""
import json, os, re, subprocess, time, urllib.request, datetime, threading
from concurrent.futures import ThreadPoolExecutor

ROOT = 'C:/Users/leona/projects/pequalnp-proofs'
os.chdir(ROOT)
BASH = 'C:/Program Files/Git/bin/bash.exe'
D = '.pnp/rep44'
STATE = D + '/worker_state.json'
PAT = re.compile(r'∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.FanInTwo C ∧ C\.size ≤ (\d+) ∧ '
                 r'PEqualNP\.Represents\.Represents \(fun u v : Fin (\d+) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) C$')
ENV = dict(os.environ, PATH=ROOT + '/.pnp/windows-bin:' + os.environ.get('PATH', ''))
lock = threading.Lock()

def say(*a):
    with lock:
        with open(D + '/worker.log', 'a', encoding='utf-8') as f:
            f.write(time.strftime('%H:%M:%S ') + ' '.join(str(x) for x in a) + '\n')

def load():
    try: return json.load(open(STATE, encoding='utf-8'))
    except Exception: return {}
def save(st):
    with lock:
        json.dump(st, open(STATE, 'w', encoding='utf-8'), indent=0)

def gates_ok(k, mask, gates, s):
    n = 2 * k; out = n + len(gates) - 1
    if len(gates) > s: return False
    for u in range(k):
        for v in range(k):
            w = [i == u for i in range(k)] + [j == v for j in range(k)]
            for o, a, b in gates:
                w.append((w[a] and w[b]) if o == 0 else (w[a] or w[b]) if o == 1 else (not w[a]))
            if w[out] != bool((mask >> (k * u + v)) & 1): return False
    return True

def lean_block(num, k, gates):
    ops = {0: 'and', 1: 'or', 2: 'not'}
    gl = ', '.join('⟨GateOp.%s, [%s]⟩' % (ops[o], str(a) if o == 2 else '%d, %d' % (a, b)) for o, a, b in gates)
    ns = 'PEqualNP.Outside.L_meta_%s.Helpers' % num
    block = (f'namespace {ns}\n\nopen PEqualNP.CircuitLowerBounds\n\n'
             f'/-- A {len(gates)}-gate circuit found by SAT-based exact synthesis: inputs 0..{k-1} are the left vertex,\n'
             f'{k}..{2*k-1} the right vertex, gate `j` writes wire `{2*k} + j`, the output is the last gate. -/\n'
             f'def witness : Circuit :=\n  ⟨[{gl}], {2*k + len(gates) - 1}⟩\n\nend {ns}\n\n')
    proof = (f'  refine ⟨{ns}.witness, ?_, by decide, by decide⟩\n'
             f'  simp [PEqualNP.MetaComplexity.FanInTwo, {ns}.witness]\n')
    return block, proof

def splice(src, block, proof):
    i = src.index('theorem ')
    src = src[:i] + block + src[i:]
    assert src.rstrip().endswith('sorry')
    return src.rstrip()[:-len('sorry')].rstrip() + '\n' + proof

def sat(num, k, s, mask):
    h = format(mask, 'x')
    cmd = (f"cd ~/ns && TAG=rw_{num}_ timeout 700 python3 synth_sat3.py {2*k} rel:{k}:{h} {s} 1 "
           f"~/cadical/build/cadical cnfrw 650 | head -40")
    out = subprocess.run(['wsl.exe', '-e', 'bash', '-lc', cmd], capture_output=True, text=True).stdout
    first = out.strip().splitlines()[0] if out.strip() else ''
    if not first.startswith('SAT'):
        return first.split()[0] if first else 'ERR', None
    gates = [tuple(map(int, l.split())) for l in out.splitlines()[1:] if re.match(r'^[012] -?\d+ -?\d+$', l.strip())]
    return 'SAT', gates

def local_check(fn):
    r = subprocess.run(['lake', 'env', 'lean', os.path.abspath(fn)], cwd='lean', capture_output=True, text=True)
    return r.returncode == 0 and 'error' not in r.stdout

def pnp(*args, timeout=120):
    r = subprocess.run([BASH, 'tools/pnp.sh'] + list(args), capture_output=True, text=True, env=ENV, timeout=timeout)
    return r.stdout + r.stderr

def handle(gid, stmt, st):
    num = gid.split('-')[-1]
    m = PAT.match(stmt)
    s, k, mask, mult = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4))
    rec = st.setdefault(gid, {})
    if 'gates' not in rec:
        if k != mult or k > 5:
            rec['status'] = 'skip-shape'; return
        res, gates = sat(num, k, s, mask)
        if res != 'SAT':
            rec['status'] = 'nosat-' + res; say(gid, 'SAT result', res); return
        if not gates_ok(k, mask, gates, s):
            rec['status'] = 'bad-witness'; say(gid, 'witness failed python check'); return
        rec['gates'] = gates; rec['k'] = k; rec['s'] = s
        say(gid, 'SAT', len(gates), 'gates (bound', s, ')')
    if not rec.get('local_ok'):
        block, proof = lean_block(num, k, [tuple(g) for g in rec['gates']])
        src = 'import Mathlib\nimport PEqualNP.Defs\n\ntheorem PEqualNP.Outside.L_meta_%s : (%s) := by\n  sorry\n' % (num, stmt)
        fn = D + '/W_L_meta_%s.lean' % num
        open(fn, 'w', encoding='utf-8', newline='\n').write(splice(src, block, proof))
        if not local_check(fn):
            rec['status'] = 'local-fail'; say(gid, 'LOCAL CHECK FAILED'); return
        rec['local_ok'] = True; say(gid, 'local Lean check passed')
    rec['status'] = 'ready'

def try_submit(gid, st):
    rec = st[gid]; num = gid.split('-')[-1]
    if os.path.exists(D + '/submitted_' + num) and not rec.get('submitted'):
        rec['submitted'] = 'by batch_go'; return
    if rec.get('submitted') or rec.get('status') != 'ready': return
    if rec.get('retry_after') and datetime.datetime.now(datetime.timezone.utc).isoformat() < rec['retry_after']:
        return
    f = 'lean/PEqualNP/Outside/L_meta_%s.lean' % num
    closed = open('.pnp/closed_steps.txt', encoding='utf-8').read().split() if os.path.exists('.pnp/closed_steps.txt') else []
    if gid in closed:
        rec['status'] = 'closed'; return
    out = pnp('next', '--proof-of', gid)
    if re.search(r'not open|proved first|just proved|already on main|stood down', out):
        rec['status'] = 'closed'; say(gid, 'closed on the desk; never retried')
        with open('.pnp/closed_steps.txt', 'a', encoding='utf-8') as fc: fc.write(gid + '\n')
        return
    time.sleep(8)
    if '429' in out or 'Too Many' in out:
        later = datetime.datetime.now(datetime.timezone.utc) + datetime.timedelta(seconds=90)
        rec['retry_after'] = later.isoformat(); say(gid, 'rate limited (429); retry after', later.strftime('%H:%M:%S'))
        time.sleep(30); return
    m = re.search(r'Bring your proof back after (\S+?)Z', out)
    if m:
        rec['retry_after'] = m.group(1) + '+00:00'; say(gid, 'held by another agent; retry after', m.group(1)); return
    if not (os.path.exists(f) and 'sorry' in open(f, encoding='utf-8').read()):
        rec['status'] = 'no-skeleton'; say(gid, 'no skeleton:', out.strip().splitlines()[:2]); return
    block, proof = lean_block(num, rec['k'], [tuple(g) for g in rec['gates']])
    open(f, 'w', encoding='utf-8', newline='\n').write(splice(open(f, encoding='utf-8').read(), block, proof))
    pnp('check', gid, timeout=900)
    if not os.path.exists('.pnp/%s.checked' % gid):
        rec['status'] = 'desk-check-fail'; say(gid, 'DESK CHECK FAILED'); return
    r = subprocess.run([BASH, '.pnp/scratch/fastsubmit.sh', gid], capture_output=True, text=True, env=ENV, timeout=400)
    url = [l for l in (r.stdout + r.stderr).splitlines() if l.startswith('https://')]
    if url:
        rec['submitted'] = url[0]; say(gid, 'SUBMITTED', url[0])
    else:
        say(gid, 'submit gave:', (r.stdout + r.stderr).strip().splitlines()[:3])
        if 'proved' in r.stdout + r.stderr or 'already on main' in r.stdout + r.stderr:
            rec['status'] = 'proved-first'

def main():
    st = load(); say('worker started; known', len(st))
    while True:
        try:
            req = urllib.request.Request('https://data.pequalnp.com/data/desk/gaps.json', headers={'User-Agent': 'curl/8.0'})
            with urllib.request.urlopen(req, timeout=60) as r:
                G = json.load(r)['gaps']
            live = {g['id']: (g.get('statement') or '').strip() for g in G}
            todo = [(gid, s) for gid, s in live.items() if PAT.match(s) and gid not in st]
            if todo:
                say('new steps:', len(todo))
                with ThreadPoolExecutor(4) as ex:
                    list(ex.map(lambda a: handle(a[0], a[1], st), todo))
                save(st)
            for gid in list(st):
                if gid in live and st[gid].get('status') == 'ready' and not st[gid].get('submitted'):
                    try_submit(gid, st); save(st)
                elif gid not in live and st[gid].get('status') == 'ready' and not st[gid].get('submitted'):
                    st[gid]['status'] = 'gone'; save(st)
        except Exception as e:
            say('loop error', type(e).__name__, str(e)[:200])
        time.sleep(30)

main()
