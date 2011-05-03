load ../../../../k-prelude
load cink-semantics

kmod CINK is including CINK-SEMANTICS
---running a program identified by its name, maybe with an input list
  syntax Bag ::= run ( KLabel ) | run ( KLabel , List{K} )
  rule run ( L:KLabel )
       =>
       <T_> <k> L(.List{K}) </k> <_/T>
       [structural]

  rule run ( L:KLabel , Il:List{K} )
       =>
       <T_> <k> L(.List{K}) </in> <_/T>
       [structural]
endkm
