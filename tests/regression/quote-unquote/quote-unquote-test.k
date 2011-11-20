require /modules/quote-unquote

require /modules/exp
require /modules/if
require /modules/lambda
require /modules/mu
require /modules/seq
require /modules/ref
require /modules/io
require /modules/while

require /modules/uris

module QUOTE-UNQUOTE-TEST imports QUOTE-UNQUOTE + IO + WHILE + REF + MU + LAMBDA + EXP + URIS
  configuration <T><k> $PGM:K </k> <mem>.Map</mem> <nextLoc>0</nextLoc><in stream="stdin">.List</in><out stream="stdout">.List</out></T>
end module
