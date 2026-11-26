#!/bin/bash
# usage: wave_solve2.sh listfile secs   (list lines: num k s mask)
# Solves each step with AND/OR/NOT SAT, 8 at a time; prints "RES num STATUS o,a,b;o,a,b;..." as each one finishes.
cd ~/ns || exit 1
one() {
  set -- $1; h=$(printf '%x' $4)
  out=$(TAG=wr_$1_ timeout $(( $5 + 15 )) python3 synth_sat3.py $((2*$2)) rel:$2:$h $3 1 ~/cadical/build/cadical cnfrace $5 2>&1)
  st=$(printf '%s\n' "$out" | head -1 | awk '{print $1}')
  g=$(printf '%s\n' "$out" | grep -E '^[012] -?[0-9]+ -?[0-9]+$' | tr ' ' ',' | tr '\n' ';')
  echo "RES $1 ${st:-ERR} $g"
}
export -f one
sed 's/\r$//' "$1" | awk -v t=$2 'NF>=4 {print $1" "$2" "$3" "$4" "t}' | xargs -P 8 -I{} bash -c 'one "{}"'
