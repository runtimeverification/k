#!/bin/sed -f

# Lexer for Lazy K

# Usage:  $ cat program.lazy | sed -f lexer.sed > program.lexed.unl


# Written for GNU sed.


# This lexer converts a Lazy-K program into a K-readable equivalent.
# * Comments and extra whitespace are removed.
# * Undefined characters are indicated as an "UNDEF" token.
# * The combinator application token "`" is replaced by "=".
# * "I" -> "!".
# * "i" -> "j".
# * "K" and "S" to lowercase.
# * "0" and "1" to "z" and "o" respectively.
# * Converts parens to brackets.
# * Introduces spaces between adjacent tokens.
# * Adds "write" token at beginning (requires at least one line in input).
# * Adds "read" token at end.




# Remove comments
s/#.*//


# Remove whitespace
s/\s//g


# Add spaces after remaining commands
s/./& /g


# Mark undefined
s/[^ iksIKS`*()01]/UNDEF/g



# Convert apply token from "`" to ">" (can't be implemented directly in K)
y/`/>/

# Convert "I" to "!"; capitals cause errors
y/I/!/

# Convert "i" to "j"; bizarre kompilation error otherwise
y/i/j/

# Convert "K" and "S" to lowercase; equivalent
y/KS/ks/

# Convert "0"/"1" to "z"/"o"; parsing ambiguity in K
y/01/zo/

# Convert parens to brackets
y/()/[]/


# "write" at beginning
1iwrite

# "read" at end
$aread

# Delete empty lines
/^$/d
