#!/bin/bash
# usage: runrep.sh tag n m hex allowNot sizes...
cd ~/ns
tag=$1; n=$2; m=$3; hx=$4; nt=$5; shift 5
for s in "$@"; do
  /usr/bin/time -f '%e s' ./repsearch "$n" "$m" "$hx" "$s" "$nt" > "rep_${tag}_${s}.txt" 2>&1
  grep -q FOUND "rep_${tag}_${s}.txt" && break
done
echo done > "rep_${tag}.done"
