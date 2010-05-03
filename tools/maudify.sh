#/bin/bash
if [ $# -eq 0 ]; then 
  FILE="/dev/stdin"
else
  FILE="$1"
fi
cat "$FILE" | sed -e :a -e '$!N; s/\n/ (KEOLN)/g; ta' | sed 's/(KEOLN)[ ]\+(KEOLN)/(KEOLN)/g' | sed 's/(KEOLN)[ ]*\(context \|rule \|configuration \|op \|mb \|eq \|rl \|ceq \|crl \|cmb \|endm\|---\)/\n  \1/g' | sed 's/\.[ ]\+\(context \|rule \|configuration \|op \|mb \|eq \|rl \|ceq \|crl \|cmb \|endm\|---\)/.\n  \1/g' | sed 's/^\([ ]*\)\(context \|rule \|configuration \)\(.*\)\(\[[ ]*metadata \)\(.*\)\.[ ]*$/\1mb \2\3: KSentence \4\5 ./g' | sed 's/^\([ ]*\)\(context \|rule \|configuration \)\(.*\)\.[ ]*$/\1mb \2\3 : KSentence ./g' | sed 's/<\(\/\?\)[ ]*\([^ <>]\+\)[ ]*\*[ ]*>/ <\1 \2 * > /g' | sed 's/<\(\/\?\)[ ]*\([^ <>]\+\)[ ]*>/ <\1 \2 > /g' | sed 's/>[ ]\+\.\.\./>... /g ; s/\.\.\.[ ]\+<\// ...<\//g' | sed 's/ (KEOLN)/\n/g' 
