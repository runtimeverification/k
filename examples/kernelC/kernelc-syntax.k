kmod KERNELC-SYNTAX is
  including PL-INT +  PL-ID
  syntax Exp ::= Int | Id
               | Exp + Exp [gather (E e) prec 33 strict] | Exp - Exp [gather (E e) prec 33 strict]
               | Exp == Exp [prec 37 strict] | Exp != Exp [prec 37 strict] 
               | Exp <= Exp [prec 37 strict] 
               | `! Exp | Exp && Exp | Exp `|| Exp | Exp `? Exp : Exp [prec 39] 
               | Exp = Exp [strict(2) prec 40 gather (e E)] | printf ( "%d;" , Exp ) [strict] 
               | scanf ( "%d" , Exp ) [strict] | & Id
               | Id ( List{Exp} ) [prec 0 strict(2)] | Id ( ) [prec 0]

--- malloc additions
  syntax Exp ::= null | free ( Exp ) [strict] | * Exp [prec 25 strict] | malloc ( Exp ) [strict] 
               | sizeof ( Exp ) [strict]

--- thread additions
  syntax Exp ::= spawn Exp | acquire ( Exp ) [strict] | release ( Exp ) [strict]

  syntax Stmt ::= Exp ; [prec 45 strict] | { } | { StmtList } | if ( Exp ) Stmt [prec 47]
                | if ( Exp ) Stmt else Stmt [prec 46 strict(1)]
                | while ( Exp ) Stmt
                | void Id List{Id} { int List{Id} ; StmtList }
                | int Id List{Id} { int List{Id} ; StmtList return Exp ; }
                | void Id List{Id} { StmtList }
                | int Id List{Id} { StmtList return Exp ; }

  syntax Id ::= main

  syntax StmtList ::= Stmt | StmtList StmtList [prec 100 gather (e E)]

  syntax Pgm ::= #include <stdio.h> #include <stdlib.h> StmtList [prec 120] 

  syntax List{Id} ::= () | Id | List{Id} , List{Id} [assoc id: () strict hybrid]
  syntax List{Exp} ::= Exp | List{Id} | List{Exp} , List{Exp} [ditto]
endkm

kmod KERNELC-DESUGARED-SYNTAX is including KERNELC-SYNTAX 
  macro ! E:Exp = E ? 0 : 1
  macro E1:Exp && E2:Exp = E1 ? E2 : 0
  macro E1 || E2 = E1 ? 1 : E2
  macro if(E) St:Stmt = if(E) St else {}
  macro null = 0
  macro I:Id () = I (())
  macro void I(L:List{Id}) { Sts:StmtList } = void  I(L:List{Id}) { int (); Sts:StmtList } 
  macro int I(L:List{Id}) { Sts:StmtList return E ;} = int  I(L:List{Id}) { int (); Sts:StmtList return E ; } 
  macro void  I(L) { int L' ; Sts } =  int  I(L:List{Id}) { int L':List{Id} ; Sts return void ;} 
  syntax Exp ::= void
endkm




