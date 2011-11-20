require /modules/callcc

require /modules/exp
require /modules/if

module CALLCC-TEST imports  CALLCC + LAMBDA + IF + EXP 
  configuration <k> $PGM:K </k> 
end module
