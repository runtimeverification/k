#!/bin/bash
MAUDE="maude"
function usage {
  echo "usage: $0 <source_file>[.maude] [<module_name>]
  
  If <module_name> is not specified, is asumed to be allcaps(<source_file>).
  <source_file> should ensure that a module <module_name> is loaded.
  Module <module_name> should contain the entire definition of the language.
  Output is printed in <source_file>-compiled.maude.
  
  If an error occurs in the compilation process (including warnings such as Module redefined), the script will stop, displaying the input, the (maybe partial) generated output, and the error/warning messages reported by Maude.
  "
}

if [ $# -eq 0 ] || [ "$1" = "-h" ] || [ "$1" = "--help" ]; then 
  usage
  exit 1
fi
which $MAUDE 1>/dev/null 2>/dev/null
if [[ $? -ne 0 ]]; then
  echo "set MAUDE to the correct path of the maude executable in kcompile.sh on line 2"
  exit 1;
fi
MAUDE="$MAUDE -no-banner -batch -no-wrap"
echo "q" | $MAUDE >/dev/null
RUNNER=`which "$0"`
KBASE=`dirname "$RUNNER"`/..
FILE=${1/.*/}
OUTPUT_FILE="${FILE}-compiled"
IFILE="kcompile_in.txt"
EFILE="kcompile_err.txt"
OFILE="kcompile_out.txt"
TFILE="kcompile_tmp.txt"
: >"$IFILE"
: >"$EFILE"
: >"$OFILE"
: >"$TFILE"

if [[ $# -eq  2 ]]; then
  LANG="$2"
else
  LANG=`echo $FILE | tr a-z A-Z`
fi

LANG0=LANG

function addLoadPrelude {
if ! grep -q "^[[:space:]]*\(load\|in\)[[:space:]].*k-prelude\(\.maude\)\?[[:space:]]*$" "$INPUT"
then
  echo "load \"$KBASE/k-prelude\"" > $IFILE
fi
}

function cleanAndExit {
  if [[ "$1" -eq 0 ]];
  then 
    rm -f "$IFILE"
    rm -f "$EFILE"
    rm -f "$OFILE"
    rm -f "$TFILE"
  fi
  exit $1
}

function checkMaude {
  if [ -n "$3" ]; then
    printf "%s.." "$3"
  fi
  INPUT="$1"
  : > $IFILE
  addLoadPrelude
  cat "$INPUT" >> $IFILE
  echo "$2" >> $IFILE
  $MAUDE <"$IFILE" >"$OFILE" 2>"$EFILE"
  if [ -n "$(<$EFILE)" ]; 
  then 
    echo ". Error ($3) when checking that $IFILE is a valid Maude module."
    cat "$EFILE"
    echo "Aborting the compilation!"
    cleanAndExit 1
  fi
  if [ -n "$3" ]; then
    printf ". Done!\n"
  fi
}

function runMaude {
  printf "%s.." "$3"
  INPUT="$1"
  : > $IFILE
  addLoadPrelude
  cat "$INPUT" >> $IFILE
  echo "$2" >> $IFILE
  $MAUDE <"$IFILE" >"$OFILE" 2>"$EFILE"
  if [ -n "$(<$EFILE)" ]; 
  then 
    echo ". Error ($3) during the transformation phase. Input is in $IFILE"
    cat "$EFILE"
    echo "Aborting the compilation!"
    cleanAndExit 1
  fi
  if ! grep -q '[-]--K-MAUDE-GENERATED-OUTPUT-END-----' "$OFILE"
  then
    echo ". Error ($3) during the transformation phase. Input is in $IFILE"
    cat "$OFILE"
    echo "Aborting the compilation!"
    cleanAndExit 1
  fi

  sed -n "/---K-MAUDE-GENERATED-OUTPUT-BEGIN---/,/---K-MAUDE-GENERATED-OUTPUT-END-----/p" "$OFILE" | sed "1 d;$ d" >"$TFILE"
  checkMaude "$TFILE" "show module ."
  echo "load \"$KBASE/k-prelude\"" > $4
  cat "$TFILE" >> $4
  printf ". Done!\n"
}

OUTPUT="$FILE.maude"

TEST_INPUT="
show module $LANG .
"

checkMaude "$OUTPUT" "$TEST_INPUT" "Testing the input module $LANG exists"

OUTPUT="$FILE.maude"

COMPILE="
load  \"$KBASE/tools/all-tools\"
loop compile .
(compile $LANG .)
"
runMaude "$OUTPUT" "$COMPILE" "Compiling the definition" $OUTPUT_FILE.maude

echo "Compiled version of $FILE.maude written in $OUTPUT_FILE.maude. Exiting."
cleanAndExit 0
