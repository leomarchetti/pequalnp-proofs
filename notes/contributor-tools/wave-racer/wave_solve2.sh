#!/bin/bash
# usage: wave_solve2.sh listfile secs [parallel] [nice]   (list lines: num k s mask)
# Solves each step with AND/OR/NOT SAT, `parallel` at a time (default 8); prints "RES num STATUS o,a,b;o,a,b;..."
# as each one finishes. With nice=1 the searches run at the lowest CPU priority.
cd ~/ns || exit 1
P=${3:-8}; NI=${4:-0}
one() {
  set -- $1; h=$(printf '%x' $4)
  pre=""; [ "$6" = 1 ] && pre="nice -n 19"
  out=$(TAG=wr_$1_ timeout $(( $5 + 15 )) $pre python3 synth_sat3.py $((2*$2)) rel:$2:$h $3 1 ~/cadical/build/cadical cnfrace $5 2>&1)
  st=$(printf '%s\n' "$out" | head -1 | awk '{print $1}')
  g=$(printf '%s\n' "$out" | grep -E '^[012] -?[0-9]+ -?[0-9]+$' | tr ' ' ',' | tr '\n' ';')
  echo "RES $1 ${st:-ERR} $g"
}
export -f one
sed 's/\r$//' "$1" | awk -v t=$2 -v ni=$NI 'NF>=4 {print $1" "$2" "$3" "$4" "t" "ni}' | xargs -P $P -I{} bash -c 'one "{}"'
