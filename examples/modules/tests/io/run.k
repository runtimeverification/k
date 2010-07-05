load ../basic-run
load ../../io

load ../ids
load ../../exp
load ../../k-visitor
load ../../substitution
load ../../lambda
load ../../mu
load programs

kmod RUN is including IO-PROGRAMS + BASIC-RUN
  configuration <T> <k> .K </k>  <nextId> 0 </nextId>
                <in> .List </in> <out> .List </out> </T>
  syntax Bag ::= run ( KLabel , List{K} )
  macro run(KL:KLabel,L:List`{K`}) 
      = <T_> <k> KL(.List{K}) </k> <in>List(L)</in> <_/T>
endkm
