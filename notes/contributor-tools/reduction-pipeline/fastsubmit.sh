#!/bin/bash
# usage: fastsubmit.sh <gap id>   (run serially; the caller holds the git lock)
# Submits a prepared, checked proof. Other untracked proof files are parked in .pnp/hold so that
# tools/pnp.sh submit sees exactly one changed file, then restored.
# Desk etiquette (the desk paused this handle for an hour on Nov 26 for re-sending to closed steps):
#  - a step whose submit came back closed (not open / STOP / proved first / refused) is never sent again;
#  - at least 60 s between any two submits from this checkout.
set -u
cd /c/Users/leona/projects/pequalnp-proofs || exit 1
export PATH="$PWD/.pnp/windows-bin:$PATH"
id="$1"; f="lean/PEqualNP/Outside/${id//-/_}.lean"
CLOSED=.pnp/closed_steps.txt; LAST=.pnp/last_submit_epoch
touch "$CLOSED"
if grep -qx "$id" "$CLOSED"; then echo "SKIP $id: closed earlier, never resend"; exit 0; fi
# cross-process git lock: all submitters share this checkout
n=0; until mkdir .pnp/gitlock 2>/dev/null; do sleep 1; n=$((n+1)); [ $n -gt 300 ] && { echo "LOCK TIMEOUT $id"; exit 1; }; done
trap 'rmdir .pnp/gitlock 2>/dev/null' EXIT
if [ -f "$LAST" ]; then
  wait_s=$(( $(cat "$LAST") + 60 - $(date +%s) ))
  [ "$wait_s" -gt 0 ] && sleep "$wait_s"
fi
git checkout -q main
mkdir -p .pnp/hold .pnp/hold_other
for o in $(git status --porcelain | sed -n 's/^?? //p' | grep '^lean/PEqualNP/Outside/' | grep -v "^$f\$"); do mv "$o" .pnp/hold/; done
# any other untracked path outside .pnp (stray outputs) is parked too, then restored
for o in $(git status --porcelain | sed -n 's/^?? //p' | grep -v '^\.pnp/' | grep -v "^$f\$" | grep -v '^lean/PEqualNP/Outside/'); do
  [ -f "$o" ] && echo "parking stray $o" && mv "$o" .pnp/hold_other/
done
if [ "${DRY:-0}" = 1 ]; then
  echo "DRY: submit would see: $(git status --porcelain | grep -v '^?? \.pnp/' | tr '\n' ';')"
else
  date +%s > "$LAST"
  out=$(timeout 150 bash tools/pnp.sh submit "$id" 2>&1)
  echo "$out" | grep -E "^https|submitted|STOP|stopped|refused|proved|not submitted|not open|paused|429" | head -3
  if ! echo "$out" | grep -q '^https'; then
    if echo "$out" | grep -qiE "not open|STOP|stopped|proved|refused|withdrawn"; then echo "$id" >> "$CLOSED"; fi
  fi
fi
git checkout -q main
for h in .pnp/hold/*.lean; do [ -e "$h" ] && mv "$h" lean/PEqualNP/Outside/; done
for h in .pnp/hold_other/*; do [ -e "$h" ] && mv "$h" .; done
echo "[$(date -u +%T)] done $id"
