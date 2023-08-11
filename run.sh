#!/usr/bin/bash

set -o pipefail

PYTHON=python3
IDRIS=idris2

infile=$1
outfile=$2
outfile="${outfile:=Main.idr}"

n=$(echo ${outfile%".idr"} | wc -c)

cmd=$($PYTHON stlc.py "$infile" "$outfile")
$IDRIS $outfile -c 2&> /dev/null

if [ $? -gt 0 ]; then
    $IDRIS $outfile -c;
else
    echo "$cmd" | $IDRIS $outfile -q | head -n -1 | cut -c "$((n + 3))"- | sed 's/.$//' | sed G;
fi