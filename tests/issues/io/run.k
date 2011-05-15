in /modules/basic-run
in /modules/seq
in /modules/io

load ../ids
in /modules/exp
in /modules/if
in /modules/k-visitor
in /modules/substitution
in /modules/lambda
in /modules/mu
load programs

kmod RUN is including IO-PROGRAMS + BASIC-RUN
  configuration <T> <k> .K </k>  <nextId> 0 </nextId>
                <in> .List </in> <out> .List </out> </T>
  syntax Bag ::= run ( KLabel , List{K} )
  macro run(KL:KLabel,L:List`{K`}) 
      = <T_> <k> KL(.List{K}) </k> <in>List(L)</in> <_/T>
endkm
