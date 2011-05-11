load ../../../../k-prelude
load pcf-untyped-syntax
load pcf-untyped-semantics
load pcf-untyped-programs

kmod PCF-UNTYPED is including PCF-UNTYPED-PROGRAMS

  // operator for running the semantics
  syntax Bag ::= [[ KLabel ]] [latex "\llbracket\,{#1}\,\rrbracket"]
  macro [[KL:KLabel]] = getResult <T_> <k> KL(.List{K}) </k> <_/T>

  syntax Bag ::= getResult Bag
  syntax CellLabel ::= result
  macro getResult <T_> <k> KR:KResult </k> <_/T> = <result> KR:KResult </result>

endkm
