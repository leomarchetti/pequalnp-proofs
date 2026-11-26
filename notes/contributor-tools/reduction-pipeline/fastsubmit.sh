#!/bin/bash
# usage: fastsubmit.sh <gap id>   (run serially; the caller holds the git lock)
# Submits a prepared, checked child. Other untracked proof files are parked in .pnp/hold so that
# tools/pnp.sh submit sees exactly one changed file, then restored.
set -u
cd /c/Users/leona/projects/pequalnp-proofs || exit 1
export PATH="$PWD/.pnp/windows-bin:$PATH"
id="$1"; f="lean/PEqualNP/Outside/${id//-/_}.lean"
git checkout -q main
mkdir -p .pnp/hold
for o in $(git status --porcelain | sed -n 's/^?? //p' | grep '^lean/PEqualNP/Outside/' | grep -v "^$f\$"); do mv "$o" .pnp/hold/; done
timeout 150 bash tools/pnp.sh submit "$id" 2>&1 | grep -E "^https|submitted|STOP|refused|proved|not submitted" | head -3
git checkout -q main
for h in .pnp/hold/*.lean; do [ -e "$h" ] && mv "$h" lean/PEqualNP/Outside/; done
echo "[$(date -u +%T)] done $id"
