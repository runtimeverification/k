require /modules/seq
require /modules/threads

require /modules/exp
require /modules/if
require /modules/lambda
require /modules/halt
require /modules/io
require /modules/ref
require /modules/while

require /modules/uris

module THREADS-TEST imports THREADS + WHILE + REF + IO + LAMBDA + HALT + EXP + URIS
  configuration <T> 
                <thread multiplicity="*"> 
                  <k> $PGM:K </k> <holds> .Map </holds>
                </thread>
                <in stream="stdin"> .List </in> 
                <out stream="stdout"> .List </out>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc>
                <busy> .Set </busy> </T>
end module
