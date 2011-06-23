require /modules/basic-run
require /modules/seq
require /modules/io

require ../ids
require /modules/exp
require /modules/if
require /modules/k-visitor
require /modules/substitution
require /modules/lambda
require /modules/mu
require programs

kmod RUN is including IO-PROGRAMS + BASIC-RUN
  configuration <T> <k> .K </k>  <nextId> 0 </nextId>
                <in> .List </in> <out> .List </out> </T>
  syntax Bag ::= run ( KLabel , List{K} )
  macro run(KL:KLabel,L:List`{K`}) 
      = <T_> <k> KL(.List{K}) </k> <in>List(L)</in> <_/T>
endkm
