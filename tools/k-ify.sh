#/bin/bash
if [ $# -eq 0 ]; then 
  FILE="/dev/stdin"
else
  FILE="$1"
fi
cat "$FILE" | sed '
s/ mb / /g;s/ : KSentence / /g;
s/<\(\/\?\)[ ]\+\([^ ]\+\)[ ]\+\(\([*]\)[ ]\+\)\?>/<\1\2\4>/g
'
