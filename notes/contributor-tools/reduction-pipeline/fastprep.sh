#!/bin/bash
# usage: fastprep.sh <gap id> <prepared child .lean> <helper namespace>
# Parallel-safe half of a child submission: lease with --proof-of, splice the prepared proof into
# the desk skeleton, and run tools/pnp.sh check. No git operations. Prints PREP_OK <id> or PREP_FAIL.
set -u
cd /c/Users/leona/projects/pequalnp-proofs || exit 1
export PATH="$PWD/.pnp/windows-bin:$PATH"
id="$1"; prep="$2"; ns="$3"; f="lean/PEqualNP/Outside/${id//-/_}.lean"
S=C:/Users/leona/AppData/Local/Temp/claude/b63fcaaf61d06969/f0f3676f-665c-4227-874e-f942837d53ea/scratchpad
echo "[$(date -u +%T)] lease $id"
timeout 90 bash tools/pnp.sh next --proof-of "$id" 2>&1 | grep -E "TERMS|error|No |not" | head -2
[ -f "$f" ] || { echo "PREP_FAIL $id no skeleton"; exit 1; }
python -I -X utf8 "$S/splice_child.py" "$f" "$prep" "$ns" >/dev/null || { echo "PREP_FAIL $id splice"; exit 1; }
bash tools/pnp.sh check "$id" >/dev/null 2>&1
[ -f ".pnp/$id.checked" ] && echo "PREP_OK $id [$(date -u +%T)]" || { echo "PREP_FAIL $id check"; exit 1; }
