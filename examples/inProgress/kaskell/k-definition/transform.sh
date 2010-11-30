#!/usr/bin/env zsh

USAGE="Usage:
  transform.sh <filepath> [optional args] [...]
    <filepath> is the path the a haskell file containing the source to transform
  Additionally, there are the following optional arguments which can be supplied anywhere:
    -h (--help)
        Display this help info
    --Parse
        Only parse the file, don't do any transformations
    --Case
        Parse the file and only perform case expression transformation (as supplied in case-semantics.maude
    --Translate
        Parse the file and only perform the translations in translations.maude
    --All (defualt)
        Parse and apply all transformations
  Behavior is unspecified when conflicting options are given.
"

# Parse command line arguments, and set up their behavior
zparseopts -E -D -- -All=all             \
                    -Translate=translate \
                    -Case=case           \
                    -Parse=parse         \
                    h=showhelp           \
                    -help=showhelp       \

PARSE_SOURCES=(hsStructs.maude haskell-syntax.maude)
CASE_SOURCES=(case-semantics.maude)
TRANSLATE_SOURCES=(translations.maude)

# If not enough arguments are given, print usage
if [[ -z $1 ]]; then
    echo $USAGE
    exit 1
fi

# Set up behavior of the arguments
if [[ -n $showhelp ]]; then
    echo $USAGE
    exit 1
fi
if [[ -n $parse ]]; then
    HASKELL_SOURCES=($PARSE_SOURCES)
    echo "Parsing Only"
fi
if [[ -n $case ]]; then
    HASKELL_SOURCES=($PARSE_SOURCES $CASE_SOURCES)
    echo "Only applying case transformations"
fi
if [[ -n $translate ]]; then
    HASKELL_SOURCES=($PARSE_SOURCES $TRANSLATE_SOURCES)
    echo "Only applying translations"
fi
if [[ -n $all || (-z $case && -z $translate && -z $parse) ]]; then
    HASKELL_SOURCES=($PARSE_SOURCES $TRANSLATE_SOURCES $CASE_SOURCES)
    echo "Applying translations and case transformations"
fi



# Make a new maude file, and set it up
tmp=`mktemp`
echo "Using $tmp"
echo "set print with parentheses on ." > $tmp
out=$(hsparse $1)
echo -n "rew " >> $tmp
echo -n $out >> $tmp
echo " ." >> $tmp
echo "q" >> $tmp

# Get the directory of this script (works even in Mac OSX)
SCRIPT_DIR=$(
cd -P -- "$(dirname -- "$0")" &&
printf '%s\n' "$(pwd -P)/$(basename -- "$0")"
) || exit 1
SCRIPT_DIR=`dirname "$SCRIPT_DIR"`

K_ROOT="$SCRIPT_DIR/../../../../"

maude -no-banner -no-wrap "$K_ROOT/k-prelude.maude" $HASKELL_SOURCES $tmp | grep result
