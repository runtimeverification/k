require /modules/mu

require /modules/exp
require /modules/if
require /modules/lambda

module MU-TEST imports MU + LAMBDA + IF + EXP 
  configuration <k> $PGM:K </k> 
end module
