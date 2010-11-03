#!/bin/bash
MAUDE="maude"
function usage {
  echo "usage: $0 <source_file>[.maude] <compiled_module_name> <program_module_name> <program_name>
  
  <source_file> should ensure that modules <compiled_module_name> and
  <program_module_name> are loaded, and that module <program_module_name>
  contains a constant <program_name>.
  Output is printed in <program_name>-compiled.maude.
  
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
COMPILED_MODULE="$2"
PROGRAM_MODULE="$3"
PROGRAM="$4"
OUTPUT_FILE="${PROGRAM}-compiled"
IFILE="kcompile_in.maude"
EFILE="kcompile_err.txt"
OFILE="kcompile_out.txt"
TFILE="kcompile_tmp.txt"
: >"$IFILE"
: >"$EFILE"
: >"$OFILE"
: >"$TFILE"

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

  echo "load \"$FILE\"" >"$TFILE"
  sed -n "/---K-MAUDE-GENERATED-OUTPUT-BEGIN---/,/---K-MAUDE-GENERATED-OUTPUT-END-----/p" "$OFILE" | sed "1 d;$ d" >>"$TFILE"
  checkMaude "$TFILE" "show module ."
  cp "$TFILE" $4
  printf ". Done!\n"
}
if [ -n "${DEBUG+x}" ]; then 

OUTPUT="$FILE.maude"

TEST_INPUT="
show module $COMPILED_MODULE .
"
checkMaude "$OUTPUT" "$TEST_INPUT" "Testing the input module $COMPILED_MODULE exists"

TEST_INPUT="
show module $PROGRAM_MODULE .
"
checkMaude "$OUTPUT" "$TEST_INPUT" "Testing the input module $PROGRAM_MODULE exists"

TEST_INPUT="
red in $PROGRAM_MODULE : $PROGRAM .
"
checkMaude "$OUTPUT" "$TEST_INPUT" "Testing the input program $PROGRAM exists"

fi

OUTPUT="$FILE.maude"

COMPILE="
set include PL-BOOL off .
set include BOOL on .
load \"$KBASE/tools/prelude-extras\"
load \"$KBASE/tools/meta-k\"
load \"$KBASE/tools/printing\"

load  \"$KBASE/tools/compile-program-interface\"
---(
set print attribute on .
red in COMPILE-PROGRAM-META : compileProgram(\"$COMPILED_MODULE\",\"$PROGRAM_MODULE\",\"$PROGRAM\") .
q
---)
loop compile-program .
(compileProgram $COMPILED_MODULE $PROGRAM_MODULE $PROGRAM .)
"
runMaude "$OUTPUT" "$COMPILE" "Compiling program $PROGRAM." $OUTPUT_FILE.maude

echo "Compiled version of $FILE.maude written in $OUTPUT_FILE.maude. Exiting."
cleanAndExit 0
