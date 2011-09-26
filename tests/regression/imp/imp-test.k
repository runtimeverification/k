require /modules/seq
require /modules/if
require /modules/while

require /modules/exp
require /modules/lambda
require /modules/ref

module IMP-TEST imports WHILE + REF + LAMBDA + EXP
  configuration <T> <k> $PGM:K </k>  <nextId> 0 </nextId>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc> </T>
end module
