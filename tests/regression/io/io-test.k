require /modules/seq
require /modules/io

require /modules/exp
require /modules/if
require /modules/lambda
require /modules/mu
require /modules/uris

module IO-TEST imports IO + MU + LAMBDA + IF + EXP + URIS
  configuration <T> <k> $PGM:K </k>  <nextId> 0 </nextId>
                <in stream="stdin"> .List </in> 
                <out stream="stdout"> .List </out> </T>
end module
