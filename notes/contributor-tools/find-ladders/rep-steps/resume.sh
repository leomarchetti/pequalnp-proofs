#!/bin/bash
# After the desk pause: one probe request (the 19147 lease). On 429 wait the stated retry_after_s
# (+30 s) and probe again; only once the desk answers normally, restart the desk workers and finish
# L-meta-19147 (splice skeleton header, desk check, single submit).
set -u
cd /c/Users/leona/projects/pequalnp-proofs || exit 1
export PATH="$PWD/.pnp/windows-bin:$PATH"
LOG=.pnp/rep44/resume.log
T=$(date -u -d '2026-11-26T09:59:30Z' +%s)
until [ "$(date -u +%s)" -ge "$T" ]; do sleep 20; done
for try in 1 2 3; do
  out=$(timeout 60 bash tools/pnp.sh next --proof-of L-meta-19147 2>&1)
  echo "[$(date -u +%T)] probe $try: $(echo "$out" | grep -E 'TERMS|Another|paused|429|error|not open' | head -2 | tr '\n' ' ')" >> $LOG
  if echo "$out" | grep -q '429'; then
    s=$(echo "$out" | grep -o '"retry_after_s": *[0-9]*' | grep -o '[0-9]*$'); s=${s:-600}
    echo "[$(date -u +%T)] still paused; waiting $((s + 30)) s" >> $LOG
    sleep $((s + 30)); continue
  fi
  break
done
if echo "$out" | grep -q '429'; then echo "[$(date -u +%T)] giving up; still paused" >> $LOG; exit 1; fi
echo "[$(date -u +%T)] desk answers; restarting workers" >> $LOG
echo "[$(date -u +%T)] restarting desk workers" >> .pnp/tools/auto.log
nohup python -I -X utf8 -u .pnp/tools/auto_children.py .pnp/scratch/targets.txt >> .pnp/tools/auto.log 2>&1 &
nohup python -I -X utf8 -u .pnp/tools/auto_any.py .pnp/scratch/targets.txt >> .pnp/tools/any.log 2>&1 &
nohup python -I -X utf8 -u .pnp/rep44/rep_worker.py >> .pnp/rep44/worker_stdout.log 2>&1 &
f=lean/PEqualNP/Outside/L_meta_19147.lean; ours=.pnp/rep44/L_meta_19147.lean
if [ -f "$f" ] && grep -q sorry "$f"; then
  python -I -X utf8 - "$f" "$ours" >> $LOG 2>&1 <<'EOF'
import re, sys
skel, ours = sys.argv[1], sys.argv[2]
s = open(skel, encoding='utf-8').read(); o = open(ours, encoding='utf-8').read()
hs = re.search(r'theorem PEqualNP\.Outside\.L_meta_19147 :.*?:= by', s, re.S).group(0)
ho = re.search(r'theorem PEqualNP\.Outside\.L_meta_19147 :.*?:= by', o, re.S)
open(skel, 'w', encoding='utf-8', newline='\n').write(o[:ho.start()] + hs + o[ho.end():])
print('spliced header from skeleton')
EOF
  bash tools/pnp.sh check L-meta-19147 >> $LOG 2>&1
  if [ -f .pnp/L-meta-19147.checked ]; then
    echo "[$(date -u +%T)] 19147 CHECKED" >> $LOG
    bash .pnp/scratch/fastsubmit.sh L-meta-19147 >> $LOG 2>&1
  else
    echo "[$(date -u +%T)] 19147 CHECKFAIL" >> $LOG
  fi
else
  echo "[$(date -u +%T)] 19147: no skeleton (held by another agent or closed)" >> $LOG
fi
wait
