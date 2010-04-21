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
  exit
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
#  echo "load \"$KBASE/k-prelude\"" > $4
#  cat "$TFILE" >> $4
  cp "$TFILE" "$4"
  printf ". Done!\n"
  if [ -n "$DEBUG" ]; then
    printf "\n--------------$3--------------------\n">>log.txt
    cat "$TFILE" >>log.txt
  fi
}

OUTPUT="$FILE.maude"

TEST_INPUT="
show module $LANG .
"

checkMaude "$OUTPUT" "$TEST_INPUT" "Testing the input module $LANG exists"

OUTPUT="$FILE.maude"

DEFAULTH="
set include PL-BOOL off .
set include BOOL on .
load \"$KBASE/tools/prelude-extras\"
load \"$KBASE/tools/meta-k\"
load \"$KBASE/tools/printing\"
"

MANY_MODULES="
$DEFAULTH
load  \"$KBASE/tools/many-modules-interface\"
loop many-modules .
(manyModules $LANG $LANG .)
"
runMaude "$OUTPUT" "$MANY_MODULES" "Flattening entire definition in a single module" "$OFILE"

ANON_CONSTS="
$DEFAULTH
load \"$KBASE/tools/anon-consts-interface\"
loop anon-consts .
(resolveAnonConsts $LANG $LANG .)
"
runMaude "$OFILE" "$ANON_CONSTS" "Transforming Anonymous constants into variables" "$OFILE"

SANITY_CHECKS="
$DEFAULTH
load  \"$KBASE/tools/sanity-checks-interface\"
loop sanity-checks .
(sanityChecks $LANG .)
"

runMaude "$OFILE" "$SANITY_CHECKS" "Checking each (sub)term parses to a sort" "$OFILE"

CONTEXT_TRANSFORMERS="
$DEFAULTH
load \"$KBASE/tools/context-transformers-interface\"
loop context-transformers .
(resolveKCxt $LANG $LANG $LANG .)
"

runMaude "$OFILE" "$CONTEXT_TRANSFORMERS" "Applying Context Transformers" "$OFILE"

OPEN_CELLS="
$DEFAULTH
load \"$KBASE/tools/open-cells-interface\"
loop open-cells .
(resolveOpenCells $LANG $LANG .)
"
runMaude "$OFILE" "$OPEN_CELLS" "Transforming open cells to normal cells through anonymous variables" "$OFILE"

ANON_VARS="
$DEFAULTH
load \"$KBASE/tools/anon-vars-interface\"
loop anon-vars .
(resolveAnonVars $LANG $LANG .)
"

runMaude "$OFILE" "$ANON_VARS"  "Resolving Anonymous Variables" "$OFILE"

K_RULES="
$DEFAULTH
load \"$KBASE/tools/make-k-rules-interface\"
loop make-k-rules .
(resolveKRules $LANG $LANG .)
"

runMaude "$OFILE" "$K_RULES"  "Generating Maude rules from K rules" "$OFILE"

REMOVE_SUBLISTS="
$DEFAULTH
load \"$KBASE/tools/remove-sublists-interface\"
loop remove-sublists .
(removeSublists $LANG -SL .)
"
runMaude "$OFILE" "$REMOVE_SUBLISTS" "Removing subsorted lists" "$OFILE"

LANG="${LANG}-SL"

LISTS2WRAPPERS="
$DEFAULTH
load \"$KBASE/tools/lists-to-wrappers-interface\"
loop lists-to-wrappers .
(makeLists2wrappers $LANG -W .)
"
runMaude "$OFILE" "$LISTS2WRAPPERS" "Wrapping Syntax lists into K" "$OFILE"

LANG="${LANG}-W"

SYNTAX2K="
$DEFAULTH
load \"$KBASE/tools/syntax-to-k-interface\"
loop syntax-to-k .
(syntax2k $LANG -K .)
"
runMaude "$OFILE" "$SYNTAX2K" "Merging syntax sorts into K" "$OFILE"

LANG="${LANG}-K"

KPROPER="
$DEFAULTH
load \"$KBASE/tools/add-k-proper-interface\"
loop add-k-proper .
(addKProper $LANG -PROPER .)
"
runMaude "$OFILE" "$KPROPER" "Adding the KProper Sort" "$OFILE"

LANG="${LANG}-PROPER"

LISTS2K="
$DEFAULTH
load \"$KBASE/tools/lists-to-k-interface\"
loop lists-to-k .
(makeLists2k $LANG -L .)
"
runMaude "$OFILE" "$LISTS2K" "Merging lists sorts into K" "$OFILE"

LANG="${LANG}-L"

SUBSORTS="
$DEFAULTH
load \"$KBASE/tools/subsorts-to-wrappers-interface\"
loop subsorts-to-wrappers .
(resolveKSubsorts $LANG 0 .)
"

runMaude "$OFILE" "$SUBSORTS"  "Transforming subsorted builtins into injections" "$OFILE"

ARGUMENTS="
$DEFAULTH
load \"$KBASE/tools/homogenous-arguments-interface\"
loop homogenous-arguments .
(makeHomogenousArgs ${LANG}0 1 .)
"

runMaude "$OFILE" "$ARGUMENTS" "Wrapping non-K arguments" "$OFILE"

LABELS="
$DEFAULTH
load \"$KBASE/tools/make-all-labels-interface\"
loop make-all-labels .
(makeAllLabels ${LANG}01 -LABELS .)
"

runMaude "$OFILE" "$LABELS" "Reducing all K constructs to K labels" "$OFILE"

STRICTCXT="
$DEFAULTH
load \"$KBASE/tools/metadata-parsing\"
load \"$KBASE/tools/strict-ops2cxt-interface\"
loop strict-ops2cxt .
(strictOps2cxt ${LANG}01-LABELS ${LANG}01-LABELS .)
"

runMaude "$OFILE" "$STRICTCXT" "Generating Strictness Axioms" "$OFILE"

STRICTEQS="
$DEFAULTH
load \"$KBASE/tools/strict-cxt2eqs-interface\"
loop strict-cxt2eqs .
(strictCxt2eqs ${LANG}01-LABELS  ${LANG}01-LABELS .)
"
runMaude "$OFILE" "$STRICTEQS" "Generating Strictness Equations" "$OFILE"

printf "load \"$KBASE/k-prelude\"\n" >$OUTPUT_FILE.maude
cat "$OFILE" >> $OUTPUT_FILE.maude

echo "Compiled version of $FILE.maude written in $OUTPUT_FILE.maude. Exiting."
