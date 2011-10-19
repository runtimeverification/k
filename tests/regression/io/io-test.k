require /modules/seq
require /modules/io

require /modules/exp
require /modules/if
require /modules/lambda
require /modules/mu

module IO-TEST imports IO + MU + LAMBDA + IF + EXP
  configuration <T> <k> $PGM:K </k>  <nextId> 0 </nextId>
                <in stream="stdin"> .List </in> 
                <out stream="stdout"> .List </out> </T>
end module
