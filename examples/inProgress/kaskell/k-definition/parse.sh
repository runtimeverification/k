#!/usr/bin/env zsh

tmp=`mktemp`
echo "Using $tmp"
echo "set print with parentheses on ." > $tmp
out=$(hsparse $1)
echo -n "rew " >> $tmp
echo -n $out >> $tmp
echo " ." >> $tmp
echo "q" >> $tmp

# Get the directory of this script (works even in Mac OSX)
SCRIPT_DIR=$(
cd -P -- "$(dirname -- "$0")" &&
printf '%s\n' "$(pwd -P)/$(basename -- "$0")"
) || exit 1
SCRIPT_DIR=`dirname "$SCRIPT_DIR"`

K_ROOT="$SCRIPT_DIR/../../../../"
HASKELL_SOURCES=(hsStructs.maude haskell-syntax.maude $tmp)

maude -no-banner -no-wrap "$K_ROOT/k-prelude.maude" $HASKELL_SOURCES | grep result