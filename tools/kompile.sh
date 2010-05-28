#!/bin/bash
function usage {
  echo "usage: $0 <source_file>[.kmaude] [<module_name>]
  
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
RUNNER=`which "$0"`
KBASE=`dirname "$RUNNER"`/..
FILE=${1/.*/}
FILES=( "$FILE.kmaude" )
COUNTER=0
while [  $COUNTER -lt ${#FILES[@]} ]; do
  F=${FILES[COUNTER]}
  echo "Maudifying $F"
  FS=(`grep -e '^ *\(in\|load\).*kmaude' "$F" | sed 's/^[ ]*\(in\|load\)[ ]\+\(.*\)$/\2/g'`)
 for (( i=0; i<${#FS[@]}; i++ )) 
  do
    FILES[${#FILES[@]}]="${FS[i]}"
  done
  FF=${F/.*/}
  #echo "$KBASE/tools/maudify.sh \"$F\" | sed 's/\.kmaude//g' >\"$FF.maude\""
  "$KBASE/tools/maudify.sh" "$F" >"$FF.maude"
  let COUNTER=COUNTER+1 
done
"$KBASE/tools/kcompile.sh" "$FILE.maude"

