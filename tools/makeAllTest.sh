#!/bin/bash

if [ $# -ne 1 ]; then
    echo "Usage: `basename $0` <dir>"
    exit 1
fi
dir=$1
outdir="$dir/tests"
mkdir -p $outdir

for prog in $dir/*.simple; do
	krun --no-color --output-mode=none "$prog" > out.tmp
	newfilename=`basename $prog`
	newfile="$outdir/$newfilename.out"
	mv out.tmp $newfile
	cat $newfile
done

