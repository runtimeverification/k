require /modules/halt

require /modules/exp
require /modules/if
require /modules/lambda
require /modules/mu

module HALT-TEST imports HALT + MU + LAMBDA + IF + EXP 
  configuration <k> $PGM:K </k>
end module
