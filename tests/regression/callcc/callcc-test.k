require /modules/callcc

require /modules/exp
require /modules/if

module CALLCC-TEST imports  CALLCC + LAMBDA + IF + EXP 
  configuration <T> <k> $PGM:K </k> <nextId> 0 </nextId> </T>
end module
