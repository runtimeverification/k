load ../kernelc-syntax
load ../basic-kernelc-semantics
load standard-malloc-semantics
load ../kernelc-programs
load ../kernelc-race-detection

kmod KERNELC is including STANDARD-MALLOC-SEMANTICS + KERNELC-PROGRAMS + KERNELC-RACE-DETECTION 
  syntax Bag ::= run ( KLabel ) | run ( KLabel , List{K} )
  syntax CellLabel ::= result
  rule run ( L:KLabel ) => <T_> <k> L(.List{K}) ~> '_`(`)(main) </k> <_/T> [structural]
  rule run ( L:KLabel , I:List{K} ) => <T_> <k> L(.List{K}) ~> '_`(`)(main) </k> <in> List(I) </in> <_/T> [structural]
  rule <T_> <threads> .Bag </threads> <out> S:String </out> <_/T> => <result> S </result> [structural]
endkm
