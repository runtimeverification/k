load ../../k-prelude
kmod KERNELC-SYNTAX is
  including PL-INT +  PL-ID
  syntax PointerId ::= Id | * PointerId [prec 25 strict]
  syntax DeclId ::= int Exp [prec 40] | void PointerId [prec 40]
---  syntax DeclExp ::= DeclId | int List{PointerId} [ditto]
  syntax Exp ::= Int | PointerId
               | Exp + Exp [gather (E e) prec 33 strict] | Exp - Exp [gather (E e) prec 33 strict]
               | Exp == Exp [prec 37 strict] | Exp != Exp [prec 37 strict] 
               | Exp <= Exp [prec 37 strict] 
               | `! Exp | Exp && Exp | Exp `|| Exp | Exp `? Exp : Exp [prec 39] 
               | Exp = Exp [strict(2) prec 40 gather (e E)] | printf ( "%d;" , Exp ) [strict] 
               | scanf ( "%d" , Exp ) [strict] | scanf ( "%d" , & Exp )
               | Id ( List{Exp} ) [prec 0 strict(2)] | Id ( ) [prec 0]
               | DeclId
               | ++ Exp [prec 0]
               | Exp ++ [prec 0]
               | -- Exp [prec 0]
               | Exp -- [prec 0]

--- malloc additions
  syntax Exp ::= `NULL | free ( Exp ) [strict] | * Exp [ditto] | ( int * ) malloc ( Exp * sizeof ( int ) ) [strict] | Exp [ Exp ] [prec 0]

--- thread additions
  syntax Exp ::= spawn Exp | acquire ( Exp ) [strict] | release ( Exp ) [strict] | join ( Exp ) [strict]

  syntax Stmt ::= Exp ; [prec 45 strict] | { } | { StmtList } | if ( Exp ) Stmt [prec 47]
                | if ( Exp ) Stmt else Stmt [prec 46 strict(1)]
                | while ( Exp ) Stmt 
                | DeclId List{DeclId} { StmtList }
                | DeclId List{DeclId} { StmtList return Exp ; }
                | #include < StmtList >

  syntax Id ::= main

  syntax StmtList ::= Stmt | StmtList StmtList [prec 100 gather (e E)]

  syntax Pgm ::= StmtList 

  sort Bottom 
  syntax List{Bottom} ::= () | Bottom | List{Bottom} , List{Bottom}  [assoc id: () strict hybrid prec 45]
  syntax List{PointerId} ::= PointerId | List{Bottom} | List{PointerId} , List{PointerId} [ditto]
  syntax List{DeclId} ::= DeclId | List{Bottom} | List{DeclId} , List{DeclId} [ditto]
  syntax List{Exp} ::= Exp | List{PointerId} | List{DeclId} |  List{Exp} , List{Exp} [ditto]
endkm

kmod KERNELC-DESUGARED-SYNTAX is including KERNELC-SYNTAX 
  macro ! E:Exp = E ? 0 : 1
  macro E1:Exp && E2:Exp = E1 ? E2 : 0
  macro E1 || E2 = E1 ? 1 : E2
  macro if(E) St:Stmt = if(E) St else {}
  macro NULL = 0
  macro I:Id () = I (())
  macro DI:DeclId(DIL:List{DeclId}) { Sts:StmtList } = DI(DIL) { Sts return 0 ;}  

  macro void PI:PointerId = int PI
  macro int * PI = int PI
  macro #include<Sts> = Sts
  macro E1[E2] = *(E1 + E2)
  macro scanf("%d", & * E) = scanf("%d", E)
  macro (int * PI = E) = (int PI = E)
  macro (int X:Id = E ;) = int X ; X = E ;
  macro ++ E = (E = E + 1)
  macro -- E = (E = E + 1)
endkm




