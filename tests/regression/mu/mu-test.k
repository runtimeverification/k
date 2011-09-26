require /modules/mu

require /modules/exp
require /modules/if
require /modules/lambda

module MU-TEST imports MU + LAMBDA + IF + EXP 
  configuration <T> <k> $PGM:K </k> <nextId> 0 </nextId> </T>
  syntax KResult ::= #Id
end module
