require ../../../../k-prelude
kmod CINK-SYNTAX is
  including PL-INT +  PL-ID + K 

  /*@ \subsubsection*{Expressions.} */
  syntax DeclId ::= int Exp [prec 40] | void Id [prec 40] 
  syntax Exp ::= Int | Id
               | Exp + Exp [gather (E e) prec 33 strict]
               | Exp - Exp [gather (E e) prec 33 strict]
               | Exp == Exp [prec 37 strict]
               | Exp != Exp [prec 37 strict] 
               | Exp <= Exp [prec 37 strict] 
               | Exp < Exp [prec 37 strict] 
               | `! Exp
               | Exp && Exp
               | Exp `|| Exp
               | Exp `? Exp : Exp [prec 39] 
               | Exp = Exp [strict(2) prec 41 gather (e E)]
               | printf ( "%d;" , Exp ) [strict] 
               | `& Exp
               | scanf ( "%d" , Exp ) [strict]
               | Id ( List{Exp} ) [prec 0 strict(2)]
               | Id ( ) [prec 0]
               | DeclId
               | * Exp [strict]
               | Exp [ Exp ] [prec 29 strict(2)]
               | ( int * ) malloc ( Exp * sizeof ( int ) ) [strict]
               | free ( Exp ) [strict]
  /*@ \subsubsection*{Statements.} */
  syntax Stmt ::= Exp ; [prec 45 strict]
               | { }
               | { StmtList }
               | if ( Exp ) Stmt [prec 47]
               | if ( Exp ) Stmt else Stmt [prec 46 strict(1)]
               | while ( Exp ) Stmt 
               | return Exp ;
               | DeclId ( List{DeclId} ) { StmtList }
               | DeclId ( ) { StmtList }
               | #include <stdio.h>


  syntax Id ::= main

  syntax StmtList ::= Stmt
               | StmtList StmtList [prec 100 gather (e E)]

  /*@ Programs */
  syntax Pgm ::= StmtList 

  syntax Stmt ::= breakpoint ;

  /*@ Lists */
  sort Bottom 
  syntax List{Bottom} ::= .Bottom
               | Bottom
               | List{Bottom} , List{Bottom}  [assoc id: .Bottom strict hybrid prec 45]

  //@ List{Id} ::= | Id (, Id)*
  syntax List{Id} ::= Id
               | List{Bottom}
               | List{Id} , List{Id} [ditto]

  //@ List{DeclId} ::= | DeclId (, DeclId)*
  syntax List{DeclId} ::= DeclId
               | List{Bottom}
               | List{DeclId} , List{DeclId} [ditto]

  // List{Exp} ::= | Exp (, Exp)*
  syntax List{Exp} ::= Exp
               | List{Id}
               | List{DeclId}
               | List{Exp} , List{Exp} [ditto]
endkm

kmod CINK-DESUGARED-SYNTAX is including CINK-SYNTAX 
/*@
  Some statements or expression are syntactic sugars.
  Their semantics is given by desugaring.
*/
  macro ! E:Exp = E ? 0 : 1
  macro E1:Exp && E2:Exp = E1 ? E2 : 0
  macro E1 || E2 = E1 ? 1 : E2
  macro if(E) St:Stmt = if(E) St else {}
  macro I:Id () = I (.Bottom)
  macro _`(`)`{_`}(DeclId:DeclId, Stmts:StmtList) = DeclId (.Bottom) { Stmts }
  macro void Id:Id = int Id
  macro (int * X:Id = E ;) = (int X = E ;)
  macro (int X = E ;) = int X ; X = E ;
  macro (X = E) = (& X = E)
  macro (* E1 = E2) = (& * E1 = E2)

  macro E1[E2] = *(E1 + E2)
endkm


