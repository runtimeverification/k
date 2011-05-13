--- 33 C language constructs
kmod KERNELC-SYNTAX is
  including PL-INT +  PL-ID + K-LATEX
   /*@\section{KERNELC syntax}

       This module specifies the syntax of KERNELC.  The syntax has been kept as close to the C syntax as possible to allow a resonably large class of C programs to be parsed and executed with the KERNELC definition.  Nevertheless, the syntax is quite small, covering only 33 constructs of the C language.


   \subsection{Arithmetic expresions}
   */
  syntax Exp ::= Int | Id | DeclId
               | Exp + Exp [gather (E e) prec 33 strict] 
               | Exp - Exp [gather (E e) prec 33 strict]
               | Exp ++ [prec 0]
               | Exp == Exp [prec 37 strict] 
               | Exp != Exp [prec 37 strict] 
               | Exp <= Exp [prec 37 strict] 
               | Exp < Exp [prec 37 strict] 
               | Exp % Exp [prec 32 strict]
 //@\subsection{Logical operations}
  syntax Exp ::=  `! Exp | Exp && Exp | Exp `|| Exp 
               | Exp `? Exp : Exp [prec 39] 
  /*@ \subsection{Input/Output}
     For simplicity we syntactically restrict the {\tt printf} and {\tt scanf} to have only one, identifiable, argument.  As the \& operator is not part of the language, we opt for two versions of scanf, first for reading (local) variables and the other for reading into heap.
  */ 
  syntax Exp ::= printf ( "%d;" , Exp ) [strict] 
               | scanf ( "%d" , & Exp )
               | scanf ( "%d" , Exp ) [strict] 
  /*@ \subsection{Memory allocation and addressing}
      Again, for simplicity  we spell out a fixed syntax for malloc, using the size of integers as a multiplication factor and the result to a integer pointer.
  */
  syntax Exp ::=  `NULL
               | PointerId 
               | ( int * ) malloc ( Exp * sizeof ( int ) ) [strict] 
               | free ( Exp ) [strict] 
               | * Exp [prec 25 strict]
               | Exp [ Exp ] [prec 0]
  /*@ \subsection{Assignment}
      We have {\it Exp} in the left side to allow both assigning to variables and heap locations.
  */
  syntax Exp ::= Exp = Exp [strict(2) prec 40 gather (e E)] 
  //@ \subsection{Function invocation}
  syntax Exp ::= Id ( List{Exp} ) [prec 0 strict(2)] 
               | Id ( ) [prec 0]
  //@ \subsection{Random}
  syntax Exp ::= srandom ( Exp ) [strict]
               | random ( ) 

  //@ \subsection{Statements}
  syntax Stmt ::= { } 
                | Exp ; [prec 45 strict] 
                | { StmtList } 
                | if ( Exp ) Stmt [prec 47]
                | if ( Exp ) Stmt else Stmt [prec 46 strict(1)]
                | while ( Exp ) Stmt 
                | return Exp ; [strict]




  //@ \subsection{Function declaration}
  syntax Stmt ::= DeclId List{DeclId} { StmtList }
  /*@ \subsection{\#include pragmas}
      This is abusing the C syntax to allow splitting programs into fragments (statement lists) which are then included one in another.
  */
  syntax Stmt ::= #include < StmtList >

  syntax StmtList ::= Stmt | StmtList StmtList [prec 100 gather (e E)]

  syntax Pgm ::= StmtList 

  syntax Id ::= main

  syntax PointerId ::= Id 
                     | * PointerId [ditto]
  syntax DeclId ::= int Exp [prec 40] 
                  | void PointerId [prec 40]

  syntax StmtList ::= stdio.h | stdlib.h
  //@ The above constants are introduced so that KERNELC accepts a subset of the C programs.

  sort Bottom 
  syntax List{Bottom} ::= () | Bottom | List{Bottom} , List{Bottom}  [assoc id: () strict hybrid prec 45]
  syntax List{PointerId} ::= PointerId | List{Bottom} | List{PointerId} , List{PointerId} [ditto]
  syntax List{DeclId} ::= DeclId | List{Bottom} | List{DeclId} , List{DeclId} [ditto]
  syntax List{Exp} ::= Exp | List{PointerId} | List{DeclId} |  List{Exp} , List{Exp} [ditto]
endkm

kmod KERNELC-DESUGARED-SYNTAX is including KERNELC-SYNTAX 
  //@ \section{Desugaring}    Expressing some constructs in terms of others to reduce the amount of constructs to which semantics needs to be given.
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
  macro scanf( "%d" , & * E) = scanf("%d", E)
  macro (int * PointerId = E) = (int PointerId = E)
  macro (int X:Id = E ;) = int X ; X = E ;
  macro stdio.h = {} 
  macro stdlib.h = {}
endkm





