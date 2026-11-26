"""Take part in the normal desk flow for the small Represents FIND steps.

Every ~75 s: tools/pnp.sh next --another. If the step handed to us is a k-by-k Represents step
(k <= 5): SAT at the bound (NOT allowed), python check, splice into the desk skeleton, local Lean
check of that file, tools/pnp.sh check, single submit via fastsubmit.sh (git lock, pacing, closed-step
guard). If SAT says no circuit exists at the bound: release (statement_seems_false). Any other step:
release (other) at once. On a 429 every request stops until the stated time. Log: .pnp/rep44/poller.log
usage: python -I -X utf8 -u .pnp/rep44/next_poller.py
"""
import os, re, subprocess, time, json, datetime
ROOT = 'C:/Users/leona/projects/pequalnp-proofs'
os.chdir(ROOT)
BASH = 'C:/Program Files/Git/bin/bash.exe'
ENV = dict(os.environ, PATH=ROOT + '/.pnp/windows-bin:' + os.environ.get('PATH', ''))
LOG = '.pnp/rep44/poller.log'
PAT = re.compile(r'∃ C : PEqualNP\.CircuitLowerBounds\.Circuit, PEqualNP\.MetaComplexity\.FanInTwo C ∧ C\.size ≤ (\d+) ∧ '
                 r'PEqualNP\.Represents\.Represents \(fun u v : Fin (\d+) => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v\.val\)\) C\)?')

def say(*a):
    with open(LOG, 'a', encoding='utf-8') as f:
        f.write(time.strftime('%H:%M:%S ') + ' '.join(str(x) for x in a) + '\n')

def pnp(*args, timeout=120):
    r = subprocess.run([BASH, 'tools/pnp.sh'] + list(args), capture_output=True, text=True, env=ENV, timeout=timeout)
    return r.stdout + r.stderr

def ok(k, mask, gates, s):
    n = 2 * k; out = n + len(gates) - 1
    if len(gates) > s: return False
    for u in range(k):
        for v in range(k):
            w = [i == u for i in range(k)] + [j == v for j in range(k)]
            for o, a, b in gates:
                w.append((w[a] and w[b]) if o == 0 else (w[a] or w[b]) if o == 1 else (not w[a]))
            if w[out] != bool((mask >> (k * u + v)) & 1): return False
    return True

def sat(num, k, s, mask):
    h = format(mask, 'x')
    cmd = (f"cd ~/ns && TAG=np_{num}_ timeout 150 python3 synth_sat3.py {2*k} rel:{k}:{h} {s} 1 "
           f"~/cadical/build/cadical cnfnp 120 | head -40")
    out = subprocess.run(['wsl.exe', '-e', 'bash', '-lc', cmd], capture_output=True, text=True).stdout
    first = out.strip().splitlines()[0] if out.strip() else ''
    gates = [tuple(map(int, l.split())) for l in out.splitlines()[1:] if re.match(r'^[012] -?\d+ -?\d+$', l.strip())]
    return (first.split()[0] if first else 'ERR'), gates

def lean_parts(num, k, gates):
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

def release(gid, reason):
    out = pnp('release', gid, reason); time.sleep(10)
    f = 'lean/PEqualNP/Outside/%s.lean' % gid.replace('-', '_')
    if os.path.exists(f):
        os.makedirs('.pnp/rep44/stale', exist_ok=True)
        os.replace(f, '.pnp/rep44/stale/' + os.path.basename(f))
    say(gid, 'released', reason)

def paused_until(out):
    m = re.search(r'"retry_after_s":\s*(\d+)', out)
    return int(m.group(1)) if m else 120

SNAP = 'https://data.pequalnp.com/data/desk/gaps.json'

def rep_ids_now():
    import urllib.request
    req = urllib.request.Request(SNAP, headers={'User-Agent': 'curl/8.0'})
    with urllib.request.urlopen(req, timeout=60) as r:
        G = json.load(r)['gaps']
    return {g['id'] for g in G if PAT.search(g.get('statement') or '')}

def main():
    say('poller started (asks the desk only when new Represents steps appear)')
    seen = rep_ids_now()
    budget = 0
    while True:
        if budget <= 0:
            time.sleep(30)
            try:
                now = rep_ids_now()
            except Exception as e:
                say('snapshot error', e); continue
            fresh = now - seen; seen |= now
            if not fresh: continue
            budget = min(4, len(fresh)); say('new Represents steps:', len(fresh), '-> asking the desk up to', budget, 'times')
        budget -= 1
        out = pnp('next', '--another', '--level', 'solid', '--kind', 'prove')
        if '429' in out:
            s = paused_until(out); say('429: sleeping', s + 30, 's |', out.strip().splitlines()[-3:]); time.sleep(s + 30); continue
        m = re.search(r'^STEP\s+(L-[a-z]+-\d+)', out, re.M)
        if not m:
            say('no step:', (out.strip().splitlines() or [''])[0][:120]); budget = 0; continue
        gid = m.group(1); num = gid.split('-')[-1]
        f = 'lean/PEqualNP/Outside/%s.lean' % gid.replace('-', '_')
        time.sleep(10)
        skel = open(f, encoding='utf-8').read() if os.path.exists(f) else ''
        mm = PAT.search(skel)
        if not mm or mm.group(2) != mm.group(4) or int(mm.group(2)) > 5:
            release(gid, 'other'); time.sleep(12); continue
        s, k, mask = int(mm.group(1)), int(mm.group(2)), int(mm.group(3))
        res, gates = sat(num, k, s, mask)
        say(gid, 'handed to us; k', k, 'bound', s, 'SAT:', res, len(gates))
        if res == 'UNSAT':
            release(gid, 'statement_seems_false'); time.sleep(12); continue
        if res != 'SAT' or not ok(k, mask, gates, s):
            release(gid, 'out_of_time'); time.sleep(12); continue
        block, proof = lean_parts(num, k, gates)
        i = skel.index('theorem ')
        src = skel[:i] + block + skel[i:]
        src = src.rstrip()[:-len('sorry')].rstrip() + '\n' + proof
        with open(f, 'w', encoding='utf-8', newline='\n') as fw:
            fw.write(src)
        r = subprocess.run(['lake', 'env', 'lean', os.path.abspath(f)], cwd='lean', capture_output=True, text=True)
        if r.returncode != 0 or 'error' in r.stdout:
            say(gid, 'LOCAL CHECK FAILED', r.stdout[:200]); release(gid, 'other'); continue
        pnp('check', gid, timeout=900)
        if not os.path.exists('.pnp/%s.checked' % gid):
            say(gid, 'DESK CHECK FAILED'); continue
        q = subprocess.run([BASH, '.pnp/scratch/fastsubmit.sh', gid], capture_output=True, text=True, env=ENV, timeout=400)
        url = [l for l in (q.stdout + q.stderr).splitlines() if l.startswith('https://')]
        say(gid, 'SUBMITTED ' + url[0] if url else 'submit gave: ' + ' | '.join((q.stdout + q.stderr).strip().splitlines()[:2]))
        time.sleep(30)

main()
