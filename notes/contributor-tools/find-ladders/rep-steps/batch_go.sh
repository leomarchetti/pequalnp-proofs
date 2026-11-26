#!/bin/bash
# usage: batch_go.sh <file with step numbers>
# For each step (our proof already passed a local Lean check): lease with --proof-of, splice our
# witness and proof into the desk skeleton, run tools/pnp.sh check (up to 4 at once), then submit
# the checked ones one by one through fastsubmit.sh (which holds the git lock).
set -u
cd /c/Users/leona/projects/pequalnp-proofs || exit 1
export PATH="$PWD/.pnp/windows-bin:$PATH"
LOG=.pnp/rep44/batch.log
checked=()
for n in $(cat "$1"); do
  id="L-meta-$n"; f="lean/PEqualNP/Outside/L_meta_$n.lean"
  [ -f ".pnp/rep44/submitted_$n" ] && continue
  r=$(timeout 60 bash tools/pnp.sh next --proof-of "$id" 2>&1 | grep -E "TERMS|Another|already|No |error|proved" | head -1)
  echo "[$(date -u +%T)] lease $id: $r" >> $LOG
  sleep 3
  if [ -f "$f" ] && grep -q sorry "$f"; then
    python -I -X utf8 .pnp/rep44/mk_rep.py "$n" ".pnp/rep44/w_$n.txt" "$f" >> $LOG 2>&1 || { echo "SPLICE_FAIL $id" >> $LOG; continue; }
    ( bash tools/pnp.sh check "$id" > ".pnp/rep44/pnpcheck_$n.log" 2>&1
      [ -f ".pnp/$id.checked" ] && echo "[$(date -u +%T)] CHECKED $id" >> $LOG || echo "[$(date -u +%T)] CHECKFAIL $id" >> $LOG ) &
    while [ "$(jobs -r | wc -l)" -ge 4 ]; do sleep 2; done
  fi
done
wait
for n in $(cat "$1"); do
  id="L-meta-$n"
  if [ -f ".pnp/$id.checked" ] && [ ! -f ".pnp/rep44/submitted_$n" ]; then
    out=$(bash .pnp/scratch/fastsubmit.sh "$id" 2>&1)
    echo "[$(date -u +%T)] SUBMIT $id: $(echo "$out" | grep -E '^https|STOP|refused|proved|not submitted' | head -2 | tr '\n' ' ')" >> $LOG
    echo "$out" | grep -q '^https' && touch ".pnp/rep44/submitted_$n"
  fi
done
echo "[$(date -u +%T)] BATCH DONE" >> $LOG
