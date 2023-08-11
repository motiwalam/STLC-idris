#!/usr/bin/bash

PYTHON=python3
IDRIS=idris2

infile=$1
outfile=$2
outfile="${outfile:=Main.idr}"

n=$(echo ${outfile%".idr"} | wc -c)

cmd=$($PYTHON stlc.py "$infile" "$outfile")
echo "$cmd" | $IDRIS $outfile -q | head -n -1 | cut -c "$((n + 3))"- | sed 's/.$//' | sed G