#!/bin/bash
# usage: wave_solve2.sh listfile secs [parallel] [nice]
# list lines: num n_inputs spec size allow_not   (spec as synth_sat3.py takes it: rel:nl:hex | care:/path | hex:...)
# Solves each line with SAT, `parallel` at a time (default 8); prints "RES num STATUS o,a,b;o,a,b;..." as each one
# finishes. With nice=1 the searches run at the lowest CPU priority.
cd ~/ns || exit 1
P=${3:-8}; NI=${4:-0}
one() {
  set -- $1
  pre=""; [ "$7" = 1 ] && pre="nice -n 19"
  out=$(TAG=ex_$1_ timeout $(( $6 + 15 )) $pre python3 synth_sat3.py $2 $3 $4 $5 ~/cadical/build/cadical cnfexplore $6 2>&1)
  st=$(printf '%s\n' "$out" | head -1 | awk '{print $1}')
  g=$(printf '%s\n' "$out" | grep -E '^[012] -?[0-9]+ -?[0-9]+$' | tr ' ' ',' | tr '\n' ';')
  echo "RES $1 ${st:-ERR} $g"
}
export -f one
sed 's/\r$//' "$1" | awk -v t=$2 -v ni=$NI 'NF>=5 {print $1" "$2" "$3" "$4" "$5" "t" "ni}' | xargs -P $P -I{} bash -c 'one "{}"'
