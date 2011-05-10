load ../../../../k-prelude
load cink-syntax
load cink-programs
load cink-semantics

kmod CINK is including CINK-SYNTAX + CINK-PROGRAMS + CINK-SEMANTICS
---running a program identified by its name, maybe with an input list
  syntax Bag ::= run ( KLabel ) | run ( KLabel , List{K} )
  rule run ( L:KLabel )
       =>
       <T_> <k> L(.List{K}) ~> '_`(`)(main) </k> <_/T>
       [structural]

  rule run ( L:KLabel , Il:List{K} )
       =>
       <T_> <k> L(.List{K}) ~> '_`(`)(main) </k> <in> List(Il) </in> <_/T>
       [structural]
endkm
