#!/bin/sh
MAUDE="maude"
which $MAUDE 1>/dev/null 2>/dev/null
if [[ $? -ne 0 ]]; then
  echo "set MAUDE to the correct path of the maude executable in kcompile.sh on line 2"
  exit 1;
fi
echo "q" | $MAUDE -no-banner -batch >/dev/null
RUNNER=`which $0`
KBASE=`dirname $RUNNER`/..
FILE=${1/.*/}
OUTPUT_FILE="${FILE}-compiled"
if [[ $# -eq  2 ]]; then
  LANG=$2
else
  LANG=`echo $FILE | tr a-z A-Z`
fi

function runMaude {
  printf "%s.." "$2"
  OUTPUT=`echo "$1" | $MAUDE $KBASE/k-prelude | grep -A  10000 '^mod' | grep -B 10000 '^endm'`
  echo "$3 $OUTPUT show module ." | $MAUDE $KBASE/k-prelude >/dev/null
  printf ". Done!\n"
}

FILE_CONTENTS=$(<$FILE.maude)

CONTEXT_TRANSFORMERS="
load $KBASE/tools/context-transformers-interface
loop context-transformers .
(resolveKCxt $LANG $LANG $LANG .)
"

runMaude "$FILE_CONTENTS $CONTEXT_TRANSFORMERS" "Applying Context Transformers"

ANON_VARS="
load $KBASE/tools/anon-vars-interface
loop anon-vars .
(resolveAnonVars $LANG $LANG .)
"

runMaude "$OUTPUT $ANON_VARS"  "Resolving Anonymous Variables"

K_RULES="
load $KBASE/tools/make-k-rules-interface
loop make-k-rules .
(resolveKRules $LANG $LANG .)
"

runMaude "$OUTPUT $K_RULES"  "Generating Maude rules from K rules"

SUBSORTS="
load $KBASE/tools/subsorts-to-wrappers-interface
loop subsorts-to-wrappers .
(resolveKSubsorts $LANG 0 .)
"

runMaude "$OUTPUT $SUBSORTS"  "Transforming subsorted builtins into injections"

ARGUMENTS="
load $KBASE/tools/homogenous-arguments-interface
loop homogenous-arguments .
(makeHomogenousArgs ${LANG}0 1 .)
"

runMaude "$OUTPUT $ARGUMENTS" "Wrapping non-K arguments"

LABELS="
load $KBASE/tools/make-all-labels-interface
loop make-all-labels .
(makeAllLabels ${LANG}01 -LABELS .)
"

runMaude "$OUTPUT $LABELS" "Reducing all K constructs to K labels"

COMPILED="$OUTPUT"

STRICTCXT="
load $KBASE/tools/strict-ops2cxt-interface
loop strict-ops2cxt .
(strictOps2cxt ${LANG}01-LABELS ${LANG}-STRICTNESS .)
"

runMaude "$OUTPUT $STRICTCXT" "Generating Strictness Axioms" "$COMPILED"

STRICTEQS="
load $KBASE/tools/strict-cxt2eqs-interface
loop strict-cxt2eqs .
(strictCxt2eqs ${LANG}01-LABELS ${LANG}-STRICTNESS ${LANG}-STRICTNESS .)
"
runMaude "$COMPILED $OUTPUT $STRICTEQS" "Generating Strictness Equations" "$COMPILED"

TEST="
$COMPILED

$OUTPUT
mod ${LANG}-TEST is
  including ${LANG}01-LABELS .
  including ${LANG}-STRICTNESS .
endm
"

runMaude "$TEST" "Putting everything together"

echo "
load $KBASE/k-prelude
$TEST
" > $OUTPUT_FILE.maude

