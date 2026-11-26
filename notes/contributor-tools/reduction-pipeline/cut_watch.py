"""Watch the desk for depth 0-1 steps that accept reductions; cut them by the presence of an AND gate,
prove the no-AND child automatically when a template fits, send the reduction and arm the child racer.

usage:
  python -I -X utf8 -u .pnp/tools/cut_watch.py            # loop (every 60 s), log .pnp/cuts/watch.log
  python -I -X utf8 -u .pnp/tools/cut_watch.py --once     # one pass over the current snapshot (dry: no PR)
  python -I -X utf8 -u .pnp/tools/cut_watch.py --send NUM # send the cut of L-meta-NUM whose child is
                                                          # .pnp/cuts/NUM/child.lean (hand-proved)
Only the public snapshot is polled; PRs go through gh (no desk API calls). A step is cut at most once
by us (one live reduction per agent per step) and only while it has no open PR.
"""
import json, os, re, sys, time, random, subprocess, urllib.request
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cutlib

ROOT = cutlib.ROOT
os.chdir(ROOT)
CUTS = '.pnp/cuts'; os.makedirs(CUTS, exist_ok=True)
LOG = CUTS + '/watch.log'; SEEN = CUTS + '/seen.txt'
RED = 'C:/Users/leona/projects/pnp-red'
BASH = 'C:/Program Files/Git/bin/bash.exe'
KIT = open('C:/Users/leona/projects/pnp-playbook/notes/contributor-tools/reduction-pipeline/kit_or_only.lean',
           encoding='utf-8').read().replace('PEqualNP.Outside.Kit', 'PEqualNP.Outside.ChildAO')

def say(*a):
    line = time.strftime('%H:%M:%S ') + ' '.join(str(x) for x in a)
    print(line, flush=True)
    with open(LOG, 'a', encoding='utf-8') as f: f.write(line + '\n')

def snapshot():
    req = urllib.request.Request('https://data.pequalnp.com/data/desk/gaps.json', headers={'User-Agent': 'curl/8.0'})
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.load(r)['gaps']

def eligible(g):
    s = (g.get('statement') or '').strip()
    return (str(g.get('depth')) in ('0', '1') and str(g.get('reductions')) == 'True'
            and str(g.get('pr_open')) == '0' and int(g.get('weight') or 0) > 1 and 0 < len(s) <= 1650)

# ---------- child templates ----------
DISCH = ('first | decide '
         '| (simp only [decide_eq_false_iff_not]; intro h; subst h; simp_all) '
         '| (simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]; '
         'exact ⟨fun h => by subst h; simp_all, fun h => by subst h; simp_all⟩) '
         '| simp_all | (simp; omega) | (simp_all; omega) | omega')

def graph_children(num, h2, var, kind):
    """edge template: OR-only circuit cannot reject both ends of an edge yet accept the pair"""
    P = cutlib.parse(h2)
    if not P: return []
    hy = P['hyps']
    try:
        i_ao = next(i for i, h in enumerate(hy) if re.search(r'(Monotone2|IsAO2 \(\d+ : ℕ\)) ' + var + r'$', h))
        i_no = next(i for i, h in enumerate(hy) if h.startswith('(¬(∃ (x99'))
        i_fun = next(i for i, h in enumerate(hy) if 'graphFun' in h and (('circuitFun' in h) or ('.eval' in h)))
    except StopIteration:
        return []
    hf = hy[i_fun]
    m = re.search(r'graphFun (\S+) ∅ ', hf)
    nm = re.search(r'Fin \((\d+) : ℕ\) → Bool', hf)
    if not m or not nm: return []
    G, n = m.group(1), nm.group(1)
    has_cond = bool(re.search(r'Bool\), .* → .*(circuitFun|\.eval)', hf))
    edges = [(int(a), int(b)) for a, b in re.findall(r'\(\((\d+) : ℕ\), \((\d+) : ℕ\)\)', h2)]
    edges = sorted(set(edges), key=lambda e: -min(e))[:8]          # prefer edges far from small indices
    hn = ['h%d' % i for i in range(len(hy))]
    intro = ' '.join(P['preludes'] + P['binders'] + hn)
    if kind == 'ao2':
        src = f'{hn[i_ao]}.1 g hg'
    else:
        src = f'by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ({hn[i_ao]} g hg).1'
    unfold = '  unfold PEqualNP.MetaComplexity.circuitFun at fa fb fab\n' if 'circuitFun' in hf else ''
    out = []
    for (u, v) in edges:
        fu = f'(fun i : Fin {n} => decide (i = {u}))'
        fv = f'(fun i : Fin {n} => decide (i = {v}))'
        fuv = f'(fun i : Fin {n} => decide (i = {u}) || decide (i = {v}))'
        arg = (lambda f: f'{hn[i_fun]} {f} (by {DISCH})') if has_cond else (lambda f: f'{hn[i_fun]} {f}')
        body = f"""{KIT}

theorem child_{num} : {h2} := by
  intro {intro}
  have onlyOr : ∀ g ∈ {var}.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := {src}
    rcases hop with hA | hO
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      exact ({hn[i_no]} ⟨⟨i, hi⟩, by simpa using hA⟩).elim
    · exact hO
  have fa := {arg(fu)}
  have fb := {arg(fv)}
  have fab := {arg(fuv)}
  have ga : PEqualNP.MetaComplexity.NestedCover.graphFun {G} ∅ {fu} = false := by decide +kernel
  have gb : PEqualNP.MetaComplexity.NestedCover.graphFun {G} ∅ {fv} = false := by decide +kernel
  have gab : PEqualNP.MetaComplexity.NestedCover.graphFun {G} ∅ {fuv} = true := by decide +kernel
  have split := PEqualNP.Outside.ChildAO.splitEval {var} onlyOr {fu} {fv}
{unfold}  rw [fa, fb, fab, ga, gb, gab] at split
  simp at split
"""
        out.append(('graph_%d_%d' % (u, v), body, 'PEqualNP.Outside.ChildAO'))
    return out

def generic_children(num, h2):
    d = f'{CUTS}/{num}/gen'; os.makedirs(d, exist_ok=True)
    sf = f'{CUTS}/{num}/h2.txt'
    r = subprocess.run(['python', '-I', '-X', 'utf8', '.pnp/gen/gen_generic.py', sf, d, 'c' + num],
                       capture_output=True, text=True)
    res = []
    for fn in r.stdout.split():
        body = open(fn, encoding='utf-8').read().replace(f'theorem child_c{num}', f'theorem child_{num}')
        res.append(('gen_' + os.path.basename(fn), body, 'PEqualNP.Outside.GenKit'))
    return res

def prove_child(num, h2, var, kind):
    cands = graph_children(num, h2, var, kind) + generic_children(num, h2)
    if not cands: return None
    d = f'{CUTS}/{num}/try'; os.makedirs(d, exist_ok=True)
    paths = []
    for name, body, ns in cands:
        p = f'{d}/{name}.lean'
        open(p, 'w', encoding='utf-8', newline='\n').write(body)
        paths.append((p, ns))
    with ThreadPoolExecutor(4) as ex:
        res = list(ex.map(lambda t: cutlib.lean_ok(t[0]), paths))
    for (p, ns), (ok, err) in zip(paths, res):
        if ok:
            return p, ns
    say(f'L-meta-{num}', 'no template proved the child; first error:', res[0][1] if res else '')
    return None

# ---------- sending ----------
def send(num, child, ns, dry=False):
    gid = f'L-meta-{num}'
    st = open(f'{CUTS}/{num}/st.txt', encoding='utf-8').read()
    h1 = open(f'{CUTS}/{num}/h1.txt', encoding='utf-8').read()
    h2 = open(f'{CUTS}/{num}/h2.txt', encoding='utf-8').read()
    P = cutlib.parse(st)
    subprocess.run(['git', '-C', RED, 'fetch', '-q', 'upstream', 'main'])
    taken = subprocess.run(['git', '-C', RED, 'ls-tree', '--name-only', 'upstream/main', 'lean/PEqualNP/Outside/'],
                           capture_output=True, text=True).stdout
    k = next(k for k in random.sample(range(800, 999), 150) if f'R_meta_{num}_{k}.lean' not in taken)
    rf = f'{CUTS}/{num}/R_meta_{num}_{k}.lean'
    open(rf, 'w', encoding='utf-8', newline='\n').write(cutlib.reduction_file(num, k, st, h1, h2, P))
    ok, err = cutlib.lean_ok(rf)
    if not ok:
        say(gid, 'REDUCTION BUILD FAIL', err); return False
    if dry:
        say(gid, 'DRY: reduction and child both compile; would send R_meta_%s_%d' % (num, k)); return True
    f = f'lean/PEqualNP/Outside/R_meta_{num}_{k}.lean'
    sh = f"""set -e
cd {RED}
git checkout -q --detach upstream/main
cp {ROOT}/{rf} {f}
eval "$(sed -n '/^format_py()/,/^}}/p' {ROOT}/tools/pnp.sh)"
python3 -I -c "$(format_py)" "$PWD/{f}" {f} {ROOT}/.pnp/scratch/fake_state.json
git checkout -q -b R-meta-{num}-{k}
git add {f}
git commit -q -m R-meta-{num}-{k}
git push -q -u origin R-meta-{num}-{k}
"""
    env = dict(os.environ, PATH=ROOT + '/.pnp/windows-bin:' + os.environ.get('PATH', ''))
    r = subprocess.run([BASH, '-c', sh], capture_output=True, text=True, env=env)
    if r.returncode != 0:
        say(gid, 'PUSH/FORMAT FAIL', (r.stdout + r.stderr)[-300:])
        subprocess.run(['git', '-C', RED, 'checkout', '-q', '--detach', 'upstream/main'])
        return False
    body = (f"**Gap id**: {gid}\n\n**The one file this adds**: {f}\n\n**Agent used**:\n- Claude Code\n\n"
            "**Checklist**\n- [x] This pull request adds exactly one file and edits no other file.\n"
            "- [x] It is a reduction: one theorem, two hypotheses, conclusion the step's statement verbatim.\n"
            "- [x] No `sorry`, no new `axiom`, no `native_decide`.\n- [x] It builds locally with the pinned toolchain.\n\n"
            "Cut by the presence of an AND gate. With no AND gate the circuit is OR-only, so its evaluation splits "
            "over a pointwise OR of inputs; that settles the second hypothesis, and a checked proof of it is ready "
            "to send when it is posted.")
    pr = subprocess.run(['gh', 'pr', 'create', '--repo', 'open-goat/pequalnp-proofs', '--head',
                         f'leomarchetti:R-meta-{num}-{k}', '--title', f'R-meta-{num}-{k} (reduction of {gid})',
                         '--body', body], capture_output=True, text=True)
    subprocess.run(['git', '-C', RED, 'checkout', '-q', '--detach', 'upstream/main'])
    url = [l for l in (pr.stdout + pr.stderr).splitlines() if l.startswith('https://')]
    if not url:
        say(gid, 'PR FAIL', (pr.stdout + pr.stderr)[-300:]); return False
    # arm the child racer
    cpath = f'{CUTS}/{num}/child.lean'
    if os.path.abspath(child) != os.path.abspath(cpath):
        open(cpath, 'w', encoding='utf-8', newline='\n').write(open(child, encoding='utf-8').read())
    with open('.pnp/scratch/targets.txt', 'a', encoding='utf-8') as t:
        t.write(f'cut{num} {CUTS}/{num}/h2.txt {cpath} {ns}\n')
    say(gid, 'SENT reduction', url[0], '| child armed in the racer')
    return True

def has_our_open_reduction(num):
    r = subprocess.run(['gh', 'pr', 'list', '-R', 'open-goat/pequalnp-proofs', '--author', 'leomarchetti',
                        '--state', 'open', '--search', f'R-meta-{num}- in:title', '--json', 'number'],
                       capture_output=True, text=True)
    return r.stdout.strip() not in ('', '[]')

def consider(g, dry=False):
    num = g['id'].split('-')[-1]
    st = g['statement'].strip()
    if 'GateOp.and' in st:          # the statement already speaks of AND gates: the cut would be degenerate
        return
    c = cutlib.cut(st)
    if not c:
        return
    if not cutlib.parse(st):
        say(g['id'], 'cut point found but the statement shape is not parsed; skipped'); return
    if has_our_open_reduction(num):
        say(g['id'], 'we already have an open reduction of it; skipped'); return
    h1, h2, var, kind, n = c
    d = f'{CUTS}/{num}'; os.makedirs(d, exist_ok=True)
    for name, txt in (('st', st), ('h1', h1), ('h2', h2)):
        open(f'{d}/{name}.txt', 'w', encoding='utf-8', newline='\n').write(txt)
    say(g['id'], 'candidate (weight %s, depth %s, %s cut on %s)' % (g.get('weight'), g.get('depth'), kind, var))
    pc = prove_child(num, h2, var, kind)
    if not pc:
        say(g['id'], 'NEEDS-CHILD: write .pnp/cuts/%s/child.lean (theorem child_%s : h2), then --send %s' % (num, num, num))
        return
    say(g['id'], 'child proved automatically by', os.path.basename(pc[0]))
    send(num, pc[0], pc[1], dry=dry)

def main():
    args = sys.argv[1:]
    if args[:1] == ['--send']:
        num = args[1]
        ns = 'PEqualNP.Outside.ChildAO'
        txt = open(f'{CUTS}/{num}/child.lean', encoding='utf-8').read()
        m = re.search(r'^namespace (\S+)', txt, re.M)
        if m: ns = m.group(1)
        ok, err = cutlib.lean_ok(f'{CUTS}/{num}/child.lean')
        if not ok:
            say(f'L-meta-{num}', 'hand child does not compile:', err); return
        send(num, f'{CUTS}/{num}/child.lean', ns); return
    once = args[:1] == ['--once']
    seen = set(open(SEEN).read().split()) if os.path.exists(SEEN) else set()
    say('cut watcher started', '(dry pass)' if once else '', 'seen', len(seen))
    while True:
        try:
            for g in snapshot():
                if g['id'] in seen or not eligible(g): continue
                seen.add(g['id'])
                if not once:
                    with open(SEEN, 'a') as f: f.write(g['id'] + '\n')
                consider(g, dry=once)
        except Exception as e:
            say('loop error', type(e).__name__, str(e)[:200])
        if once: return
        time.sleep(60)

if __name__ == '__main__':
    main()
