--- 33 C language constructs
module KERNELC-SYNTAX is
  including #INT +  #ID
---arithmetic expresions
  syntax Exp ::= Int | Id | DeclId
               | Exp + Exp [gather (E e) prec 33 strict] 
               | Exp - Exp [gather (E e) prec 33 strict]
               | Exp ++ [prec 0]
               | Exp == Exp [prec 37 strict] 
               | Exp != Exp [prec 37 strict] 
               | Exp <= Exp [prec 37 strict] 
               | Exp < Exp [prec 37 strict] 
               | Exp % Exp [prec 32 strict]
---logical operations
               | `! Exp | Exp && Exp | Exp `|| Exp 
               | Exp `? Exp : Exp [prec 39] 
---input/output
               | printf ( "%d;" , Exp ) [strict] 
               | scanf ( "%d" , Exp ) [strict] 
               | scanf ( "%d" , & Exp )
--- memory allocation and addressing
               | `NULL
               | PointerId 
               | ( int * ) malloc ( Exp * sizeof ( int ) ) [strict] 
               | free ( Exp ) [strict] 
               | * Exp [prec 25 strict]
               | Exp [ Exp ] [prec 0]
--- Assignment
               | Exp = Exp [strict(2) prec 40 gather (e E)] 
--- Function invocation
               | Id ( List{Exp} ) [prec 0 strict(2)] 
               | Id ( ) [prec 0]
--- Random 
               | srandom ( Exp ) [strict]
               | random ( ) 

  syntax Stmt ::= { } 
                | Exp ; [prec 45 strict] 
                | { StmtList } 
                | if ( Exp ) Stmt [prec 47]
                | if ( Exp ) Stmt else Stmt [prec 46 strict(1)]
                | while ( Exp ) Stmt 
                | return Exp ; [strict]




--- Function declaration
                | DeclId List{DeclId} { StmtList }
--- For fragmenting definitions into parts
                | #include < StmtList >

  syntax StmtList ::= Stmt | StmtList StmtList [prec 100 gather (e E)]

  syntax Pgm ::= StmtList 

  syntax Id ::= main

  syntax PointerId ::= Id 
                     | * PointerId [ditto]
  syntax DeclId ::= int Exp [prec 40] 
                  | void PointerId [prec 40]

--- to write C-compatible definitions
  syntax StmtList ::= stdio.h | stdlib.h

  sort Bottom 
  syntax List{Bottom} ::= () | Bottom | List{Bottom} , List{Bottom}  [assoc id: () strict hybrid prec 45]
  syntax List{PointerId} ::= PointerId | List{Bottom} | List{PointerId} , List{PointerId} [ditto]
  syntax List{DeclId} ::= DeclId | List{Bottom} | List{DeclId} , List{DeclId} [ditto]
  syntax List{Exp} ::= Exp | List{PointerId} | List{DeclId} |  List{Exp} , List{Exp} [ditto]
end module

module KERNELC-DESUGARED-SYNTAX imports KERNELC-SYNTAX 
  macro ! E:Exp = E ? 0 : 1
  macro E1:Exp && E2:Exp = E1 ? E2 : 0
  macro E1 || E2 = E1 ? 1 : E2
  macro if(E) St:Stmt = if(E) St else {}
  macro NULL = 0
  macro I:Id () = I (())
---  macro DeclId:DeclId(DeclIds:List{DeclId}) { Stmts:StmtList } = DeclId(DeclIds) { Stmts return 0 ;}  

  macro int * PointerId:PointerId = int PointerId
  macro #include<Stmts> = Stmts:StmtList
  macro E1[E2] = *(E1 + E2)
  macro scanf("%d", & * E) = scanf("%d", E)
  macro (int * PointerId = E) = (int PointerId = E)
  macro (int X:Id = E ;) = int X ; X = E ;
  macro stdio.h = {} 
  macro stdlib.h = {}
end module





