#!/bin/bash
# usage: run9.sh <size> <mode> <tables...>
cd ~/ns
S=$1; M=$2; shift 2
for t in "$@"; do
  /usr/bin/time -f '%e s' ./notsearch "$t" "$S" "$M" > "out_${t}_${S}_${M}.txt" 2>&1
done
echo done > "run_${S}_${M}.done"
