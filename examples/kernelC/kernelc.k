load ../../k-prelude
load kernelc-syntax
load kernelc-programs
load kernelc-semantics

kmod KERNELC is including KERNELC-SEMANTICS + KERNELC-PROGRAMS 
  syntax Bag ::= run ( KLabel )
  syntax CellLabel ::= result
  rule run ( L:KLabel ) => <T_> <k> L(.List{K}) </k> <_/T> [structural]
  rule <T_> <k>.K</k> <out> S:String </out> <_/T> => <result> S </result> [structural]
endkm
