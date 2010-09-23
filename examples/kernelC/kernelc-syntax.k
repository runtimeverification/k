kmod KERNELC-SYNTAX is
  including PL-INT +  PL-ID
  syntax Exp ::= Int | Id
               | Exp + Exp [gather (E e) prec 33 strict] | Exp - Exp [gather (E e) prec 33 strict]
               | Exp == Exp [prec 37 strict] | Exp != Exp [prec 37 strict] 
               | Exp <= Exp [prec 37 strict] 
               | `! Exp | Exp && Exp | Exp `|| Exp | Exp `? Exp : Exp [prec 39] 
               | Exp = Exp [strict(2) prec 40 gather (e E)] | printf ( "%d;" , Exp ) [strict]

--- malloc additions
  syntax Exp ::= null | free ( Exp ) [strict] | * Exp [prec 25 strict] | malloc ( Exp ) [strict]

  syntax Stmt ::= ; | Exp ; [prec 45 strict] | { } | { StmtList } | if ( Exp ) Stmt [prec 47]
                | if ( Exp ) Stmt else Stmt [prec 46 strict(1)]
                | while ( Exp ) Stmt
  syntax StmtList ::= Stmt | StmtList StmtList [prec 100 gather (e E)]

  syntax Pgm ::= #include <stdio.h> #include <stdlib.h> void main(void) { StmtList }
endkm

kmod KERNELC-DESUGARED-SYNTAX is including KERNELC-SYNTAX 
  macro ! E:Exp = E ? 0 : 1
  macro E1:Exp && E2:Exp = E1 ? E2 : 0
  macro E1 || E2 = E1 ? 1 : E2
  macro if(E) St:Stmt = if(E) St else {}
  macro null = 0
endkm




