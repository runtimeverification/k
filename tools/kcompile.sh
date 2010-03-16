#!/bin/bash
function usage {
  echo "usage: $0 <source_file>[.maude] [<module_name>]
  
  If <module_name> is not specified, is asumed to be allcaps(<source_file>).
  <source_file> should ensure that a module <module_name> is loaded.
  IMPORTANT: <source_file> should not load the k-prelude, as it will be loaded automatically by the script and, if loaded, will cause the script to stop.
  Module <module_name> should contain the entire definition of the language.
  Output is printed in <source_file>-compiled.maude.
  
  If an error occurs in the compilation process (including warnings such as Module redefined), the script will stop, displaying the input, the (maybe partial) generated output, and the error/warning messages reported by Maude.
  "
}

if [ $# -eq 0 ] || [ "$1" = "-h" ] || [ "$1" = "--help" ]; then 
  usage
  exit
fi
MAUDE="maude"
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
    exit
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
    exit
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

OPEN_CELLS="
load \"$KBASE/tools/open-cells-interface\"
loop open-cells .
(resolveOpenCells $LANG $LANG .)
"
runMaude "$OUTPUT $OPEN_CELLS" "Transforming open cells to normal cells through anonymous variables"



ANON_CONSTS="
load \"$KBASE/tools/anon-consts-interface\"
loop anon-consts .
(resolveAnonConsts $LANG $LANG .)
"
runMaude "$OUTPUT $ANON_CONSTS" "Transforming anonymous constants to anonymous variables"


SYNTAX2K="
load \"$KBASE/tools/syntax-to-k-interface\"
loop syntax-to-k .
(syntax2k $LANG -K .)
"
runMaude "$OUTPUT $SYNTAX2K" "Merging syntax sorts into K"

LANG="${LANG}-K"

KPROPER="
load \"$KBASE/tools/add-k-proper-interface\"
loop add-k-proper .
(addKProper $LANG -PROPER .)
"
runMaude "$OUTPUT $KPROPER" "Adding the KProper Sort"

LANG="${LANG}-PROPER"

CONTEXT_TRANSFORMERS="
load \"$KBASE/tools/context-transformers-interface\"
loop context-transformers .
(resolveKCxt $LANG $LANG $LANG .)
"

runMaude "$OUTPUT $CONTEXT_TRANSFORMERS" "Applying Context Transformers"

ANON_VARS="
load \"$KBASE/tools/anon-vars-interface\"
loop anon-vars .
(resolveAnonVars $LANG $LANG .)
"

runMaude "$OUTPUT $ANON_VARS"  "Resolving Anonymous Variables"

K_RULES="
load \"$KBASE/tools/make-k-rules-interface\"
loop make-k-rules .
(resolveKRules $LANG $LANG .)
"

runMaude "$OUTPUT $K_RULES"  "Generating Maude rules from K rules"

SUBSORTS="
load \"$KBASE/tools/subsorts-to-wrappers-interface\"
loop subsorts-to-wrappers .
(resolveKSubsorts $LANG 0 .)
"

runMaude "$OUTPUT $SUBSORTS"  "Transforming subsorted builtins into injections"

ARGUMENTS="
load \"$KBASE/tools/homogenous-arguments-interface\"
loop homogenous-arguments .
(makeHomogenousArgs ${LANG}0 1 .)
"

runMaude "$OUTPUT $ARGUMENTS" "Wrapping non-K arguments"

LABELS="
load \"$KBASE/tools/make-all-labels-interface\"
loop make-all-labels .
(makeAllLabels ${LANG}01 -LABELS .)
"

runMaude "$OUTPUT $LABELS" "Reducing all K constructs to K labels"

COMPILED="$OUTPUT"

STRICTCXT="
load \"$KBASE/tools/strict-ops2cxt-interface\"
loop strict-ops2cxt .
(strictOps2cxt ${LANG}01-LABELS ${LANG}-STRICTNESS .)
"

runMaude "$OUTPUT $STRICTCXT" "Generating Strictness Axioms" "$COMPILED"

STRICTEQS="
load \"$KBASE/tools/strict-cxt2eqs-interface\"
loop strict-cxt2eqs .
(strictCxt2eqs ${LANG}01-LABELS ${LANG}-STRICTNESS ${LANG}-STRICTNESS .)
"
runMaude "$COMPILED $OUTPUT $STRICTEQS" "Generating Strictness Equations" "$COMPILED"

TEST="
$COMPILED

$OUTPUT
mod ${LANG0}-TEST is
  including ${LANG}01-LABELS .
  including ${LANG}-STRICTNESS .
endm
"

checkMaude "$TEST" "Putting everything together"

echo "
load \"$KBASE/k-prelude\"
$TEST
" > $OUTPUT_FILE.maude

echo "Compiled version of $FILE.maude written in $OUTPUT_FILE.maude. Exiting."
