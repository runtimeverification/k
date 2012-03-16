#!/bin/bash

if [ $# -ne 1 ]; then
    echo "Usage: `basename $0` <prog>"
    exit 1
fi

prog=$1
outdir=`dirname $prog`
outdir="$outdir/tests"
# echo $outdir

mkdir -p $outdir
krun --no-color "$prog" > out.tmp
newfilename=`basename $prog`
newfile="$outdir/$newfilename.out"
# echo $newfile
# echo $out
mv out.tmp $newfile
cat $newfile


