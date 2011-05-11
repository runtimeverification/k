load ../../../../k-prelude
load pcf-untyped-syntax
load pcf-untyped-semantics
load pcf-untyped-programs

kmod PCF-UNTYPED is including PCF-UNTYPED-PROGRAMS
  /*@ \section*{Running the semantics}
  This module is the entry-point for the semantics. The macro below
  take a PCF program, puts it in the \K cell to execute, and returns
  the final result, if there is one.
  */

  syntax Bag ::= [[ KLabel ]] [latex "\llbracket\,{#1}\,\rrbracket"]
  macro [[KL:KLabel]] = getResult <T_> <k> KL(.List{K}) </k> <_/T>

  syntax Bag ::= getResult Bag
  syntax CellLabel ::= result
  macro getResult <T_> <k> KR:KResult </k> <_/T> = <result> KR:KResult </result>

endkm
