#!/bin/bash
# Monotone K4-in-K5 (care rows) at size $1, four exhaustive symmetry shards in parallel.
cd ~/ns
S=$1; T=${2:-3600}
for sh in and:0-1 or:0-1 and:0-7 or:0-7; do
  tag=${PFX}${sh//[:-]/}_
  ( r=$(TAG=$tag PSYM=$sh timeout $((T+60)) python3 synth_sat2.py 10 care:$CARE $S 0 ~/cadical/build/cadical cnf $T | head -40)
    echo "=== shard $sh size $S: $r" ) > ${PFX}${S}_${sh//[:-]/}.txt 2>&1 &
done
wait
cat ${PFX}${S}_*.txt
