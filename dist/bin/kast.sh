#!/usr/bin/env sh

case $(uname) in
Linux) OS=linux;;
Darwin) OS=macos;;
*) echo "Unknown OS $(uname)"; exit 1;;
esac
BIN=$(dirname $0)/../lib/native/$OS

#pwd >> log.txt
#echo $* >> log.txt
#echo $FK >> log.txt
#env >> log.txt

if [ "$1" = --new-kast ] ; then
  MODE="--new-kast";
  shift;
else
  MODE='';
fi

if [ -z "$1" -o ! -z "$2" -o ! -f "$1" ] ; then
  echo 'Usage: kast.sh <inputfile>';
  exit 1;
fi

INPUTFILE=$1
SORT=${KRUN_SORT:-K}
DEF=${KRUN_COMPILED_DEF:-*-kompiled}
if [ ! -d $DEF ] ; then
  if [ -z "$KRUN_COMPILED_DEF" ] ; then
    if [ "*-kompiled" = '*-kompiled' ] ; then
      echo "No compiled definitions in current directory"
    else
      echo "Multiple compiled definitions in current directory"
    fi;
  else
    echo "Definition ${KRUN_COMPILED_DEF} does not exist";
  fi;
  exit 1;
fi

KDIR=$(dirname $DEF)/.k
mkdir -p $KDIR
RAWPARSE=$(mktemp $KDIR/parseXXXXXX.baf)
if $BIN/sglr -fp -s$SORT -p $DEF/pgm/Program.tbl -i $INPUTFILE > $RAWPARSE 2> /dev/null ; then
  $BIN/implodePT < $RAWPARSE | $BIN/baffle -rb -wt | $BIN/FastKast $MODE $DEF/consTable.txt
else
  $BIN/baffle -rb -wt < $RAWPARSE | $BIN/FastKast $DEF/consTable.txt
fi
rm $RAWPARSE
