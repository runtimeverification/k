#!/bin/bash

for i in */*.k.out; do
  echo "// $i"
  d=`dirname "$i"`
  o=`basename "$i"`
  ( cd "$d"; kompile "${o%.out}" 2>&1 | diff - "$o" )
done >>x.k
