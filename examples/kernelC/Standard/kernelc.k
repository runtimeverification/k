load ../../../k-prelude
load ../kernelc-syntax
load ../kernelc-programs
load ../basic-kernelc-semantics
load standard-malloc-semantics

kmod KERNELC is including STANDARD-MALLOC-SEMANTICS + KERNELC-PROGRAMS 
  syntax Bag ::= run ( KLabel )
  syntax CellLabel ::= result
  rule run ( L:KLabel ) => <T_> <k> L(.List{K}) </k> <_/T> [structural]
  rule <T_> <k>.K</k> <out> S:String </out> <_/T> => <result> S </result> [structural]
endkm
