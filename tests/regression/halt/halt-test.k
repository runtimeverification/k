require /modules/halt

require /modules/exp
require /modules/if
require /modules/lambda
require /modules/mu

module HALT-TEST imports HALT + MU + LAMBDA + IF + EXP 
  configuration <T> <k> $PGM:K </k> <nextId> 0 </nextId> </T>
end module
