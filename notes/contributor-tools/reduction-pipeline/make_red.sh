#!/bin/bash
# usage: make_red.sh <gap number N> <k>   (run from anywhere; uses the ../pnp-red worktree)
# Writes R_meta_N_k (AND-gate split right after the Monotone2/IsAO2 hypothesis), builds it,
# runs the pnp.sh format guard, and opens the reduction PR. Only use when the no-AND child of N
# is already proved and checked (.pnp/batch/child_N.lean or .pnp/scratch/child_N.lean).
set -u
n="$1"; k="$2"
P=/c/Users/leona/projects/pequalnp-proofs; R=/c/Users/leona/projects/pnp-red
S=C:/Users/leona/AppData/Local/Temp/claude/b63fcaaf61d06969/f0f3676f-665c-4227-874e-f942837d53ea/scratchpad
export PATH="$P/.pnp/windows-bin:$PATH"
cd "$R" || exit 1
git fetch -q upstream main && git checkout -q --detach upstream/main
if git ls-tree --name-only upstream/main lean/PEqualNP/Outside/ | grep -q "R_meta_${n}_"; then echo "SKIP $n: reduction already on main"; exit 2; fi
curl -sS https://data.pequalnp.com/data/desk/gaps.json -o "$S/data/gaps_live.json"
python -I -X utf8 - "$S/data/gaps_live.json" "$n" "$k" <<'EOF' || exit 1
import json, re, sys
G = {x['id']: x for x in json.load(open(sys.argv[1], encoding='utf-8'))['gaps']}
n, k = sys.argv[2], sys.argv[3]
g = G.get('L-meta-' + n)
if not g or g.get('pr_open') or (g.get('reductions_live') or 0) >= 3 or not g.get('reductions'):
    print('SKIP', n, 'not open for a reduction now'); sys.exit(1)
s = g['statement'].strip()
if len(s) > 1650:
    print('SKIP', n, 'child would exceed the 2000-character reduce-child limit'); sys.exit(1)
m = re.search(r'(PEqualNP\.MetaComplexity\.Monotone2 x1|PEqualNP\.TopForm\.IsAO2 \(\d+ : ℕ\) x1) →', s)
anchor = m.group(0); assert s.count(anchor) == 1
A = '(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)'
h1 = s.replace(anchor, anchor + ' ' + A + ' →'); h2 = s.replace(anchor, anchor + ' (¬' + A + ') →')
open(f'lean/PEqualNP/Outside/R_meta_{n}_{k}.lean', 'w', encoding='utf-8', newline='\n').write(f"""import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_{n}_{k}
    (h1 : {h1})
    (h2 : {h2}) :
    {s} := by
  intro x1
  by_cases h : {A}
  · intros
    apply h1 <;> assumption
  · intros
    apply h2 <;> assumption
""")
EOF
f="lean/PEqualNP/Outside/R_meta_${n}_${k}.lean"
bash -c 'eval "$(sed -n "/^format_py()/,/^}/p" '"$P"'/tools/pnp.sh)"; python3 -I -c "$(format_py)" "$PWD/'"$f"'" '"$f"' '"$P"'/.pnp/scratch/fake_state.json' || { echo "FORMAT FAIL $n"; rm -f "$f"; exit 1; }
(cd "$P/lean" && lake env lean "$R/$f" >/dev/null 2>&1) || { echo "BUILD FAIL $n"; rm -f "$f"; exit 1; }
[ "${DRY:-0}" = 1 ] && { echo "DRY OK $n"; rm -f "$f"; exit 0; }
git checkout -q -b "R-meta-$n-$k" && git add "$f" && git commit -q -m "R-meta-$n-$k" && git push -q -u origin "R-meta-$n-$k" 2>/dev/null
gh pr create --repo open-goat/pequalnp-proofs --head "leomarchetti:R-meta-$n-$k" --title "R-meta-$n-$k (reduction of L-meta-$n)" --body "**Gap id**: L-meta-$n

**The one file this adds**: $f

**Agent used**:
- Claude Code

**Checklist**
- [x] This pull request adds exactly one file and edits no other file.
- [x] It is a reduction: one theorem, two hypotheses, conclusion the step's statement verbatim.
- [x] No \`sorry\`, no new \`axiom\`, no \`native_decide\`.
- [x] It builds locally with the pinned toolchain.

Cut by the presence of an AND gate. With no AND gate the circuit is OR-only, so its evaluation splits over a pointwise OR of inputs and is monotone; that settles the second hypothesis, and a checked proof of it is ready to send when it is posted." 2>&1 | grep -E "^https"
git checkout -q --detach upstream/main
