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
if [[ $# -eq  2 ]]; then
  LANG="$2"
else
  LANG=`echo $FILE | tr a-z A-Z`
fi

LANG0=LANG

function addLoadPrelude {
if ! [[ "$INPUT" =~ load\ .*k-prelude ]] && ! [[ "$INPUT" =~ in\ .*k-prelude ]] ; then
     INPUT="
load \"$KBASE/k-prelude\"
$INPUT"
fi
}

function checkMaude {
  if [ -n "$2" ]; then
    printf "%s.." "$2"
  fi
  INPUT="$1"
  addLoadPrelude
  result=$( { stdout=$(echo "$INPUT" | $MAUDE ) ; } 2>&1; printf "%s" "--------------------$stdout")
OUTPUT1=${result#*--------------------}
ERROR=${result%--------------------*}
  if [ -n "$ERROR" ]; then
    echo ". Error in encountered when passing the Input below to Maude 
Input:
$1
Output:
$OUTPUT1
Error ($2): 
$ERROR
Stopping the compilation!"
    exit 1
  fi
  if [ -n "$2" ]; then
    printf ". Done!\n"
  fi
}

function runMaude {
  printf "%s.." "$2"
  INPUT="$1"
  addLoadPrelude
  result=$( { stdout=$(echo "$INPUT" | $MAUDE ) ; } 2>&1; printf "%s" "-k-maude-delimiter--$stdout")
OUTPUT=${result#*-k-maude-delimiter--}
#echo "$OUTPUT"
OUTPUT="${OUTPUT%---K-MAUDE-GENERATED-OUTPUT-END-----*}"
#echo "$OUTPUT"
OUTPUT="${OUTPUT#*---K-MAUDE-GENERATED-OUTPUT-BEGIN---}"
#echo "$OUTPUT"
ERROR=${result%-k-maude-delimiter--*}
  if [ -n "$ERROR" ]; then
    echo ". Error encountered when generating the output module: 
Input:
$1
Output:
$OUTPUT
Error ($2): 
$ERROR
Stopping the compilation!"
    exit 1
  fi
 
  checkMaude "$3 $OUTPUT show module ."

  printf ". Done!\n"
  if [ -n "$DEBUG" ]; then
    echo "
--------------$2--------------------
$OUTPUT
" >>log.txt
  fi
}

OUTPUT=$(<$FILE.maude)

TEST_INPUT="
show module $LANG .
"

checkMaude "$OUTPUT $TEST_INPUT" "Testing the input module $LANG exists"

OUTPUT=$(<$FILE.maude)

DEFAULTH="
set include PL-BOOL off .
set include BOOL on .
set print attribute on .
load \"$KBASE/tools/prelude-extras\"
load \"$KBASE/tools/meta-k\"
load \"$KBASE/tools/printing\"
"

COMPILE="
load  \"$KBASE/tools/all-tools\"
loop compile .
(compile $LANG .)
"
runMaude "$OUTPUT $COMPILE" "Compiling the definition"

echo "
load \"$KBASE/k-prelude\"
$OUTPUT
" > $OUTPUT_FILE.maude

echo "Compiled version of $FILE.maude written in $OUTPUT_FILE.maude. Exiting."
