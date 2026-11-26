#!/bin/bash
# usage: send_red.sh <N> <K>   — submit .pnp/size/R_meta_N_K.lean as a reduction PR from ../pnp-red
# Requires .pnp/size/child_size_N.lean to have been checked (exit 0). Arms the child in targets.txt.
set -u
n="$1"; k="$2"
P=/c/Users/leona/projects/pequalnp-proofs; R=/c/Users/leona/projects/pnp-red
export PATH="$P/.pnp/windows-bin:$PATH"
f="lean/PEqualNP/Outside/R_meta_${n}_${k}.lean"
cd "$R" || exit 1
git fetch -q upstream main && git checkout -q --detach upstream/main
git ls-tree --name-only upstream/main lean/PEqualNP/Outside/ | grep -q "R_meta_${n}_${k}.lean" && { echo "SKIP $n: name taken"; exit 2; }
st=$(curl -sS "https://pequalnp.com/desk/step?gap=L-meta-$n" | python -I -c "import json,sys;print(json.load(sys.stdin).get('state'))")
[ "$st" = "open" ] || [ "$st" = "leased" ] || { echo "SKIP $n: desk state $st"; exit 2; }
cp "$P/.pnp/size/R_meta_${n}_${k}.lean" "$f"
bash -c 'eval "$(sed -n "/^format_py()/,/^}/p" '"$P"'/tools/pnp.sh)"; python3 -I -c "$(format_py)" "$PWD/'"$f"'" '"$f"' '"$P"'/.pnp/scratch/fake_state.json' || { echo "FORMAT FAIL $n"; rm -f "$f"; exit 1; }
(cd "$P/lean" && lake env lean "$R/$f" >/dev/null 2>&1) || { echo "BUILD FAIL $n"; rm -f "$f"; exit 1; }
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

Cut by circuit size. The small side (size at most the number of essential inputs minus two) is ruled out by the connectivity bound: a fan-in-two circuit whose output depends on every essential input needs at least that many gates minus one. A checked proof of that side is ready to send when it is posted; the large side carries the lower bound." 2>&1 | grep -E "^https"
git checkout -q --detach upstream/main
echo "c_s$n .pnp/size/h_small_$n.txt .pnp/size/child_size_$n.lean PEqualNP.Outside.DepKit" >> "$P/.pnp/scratch/targets.txt"
