--- 33 C language constructs
kmod KERNELC-SYNTAX is including PL-INT +  PL-ID 

/*@ \section{\KERNELC syntax}
This module specifies the syntax of \KERNELC.  The syntax has been kept 
as close to the C syntax as possible to allow a resonably large class of 
C programs to be parsed and executed with the \KERNELC definition.  
Nevertheless, the syntax is quite small, covering only 33 constructs of 
the C language. */


//@ \subsection{Arithmetic expresions}

  syntax Exp ::= Int | Id 
               | Exp + Exp [gather (E e) prec 33 strict] 
               | Exp - Exp [gather (E e) prec 33 strict]
               | Exp ++ [prec 0]
               | Exp == Exp [prec 37 strict] 
               | Exp != Exp [prec 37 strict] 
               | Exp <= Exp [prec 37 strict] 
               | Exp < Exp [prec 37 strict] 
               | Exp % Exp [prec 32 strict]

/*@ \subsection{Logical operations}
The logical operation are just syntactic sugar.  First all regular 
constructs {\tt !, \&\&, ||} are desugared into the expression 
conditional operator in the {\tt KERNELC-DESUGARED-SYNTAX} module 
(therefore, they are shortcut), and the expresion conditional operator 
is itself desugared into the statement conditional once the syntax is 
collapsed in the computation sort in the {\tt KERNELC-SEMANTICS} module. */

  syntax Exp ::=  `! Exp | Exp && Exp | Exp `|| Exp 
               | Exp `? Exp : Exp [prec 39] 

/*@ \subsection{Variable declaration}
For parsing reasons, a variable declaration in this definition of 
\KERNELC is considered an expression introduced by the type {\tt int} and 
defining an indentifier (maybe qualified as a pointer).  
The type accepted by the {\tt int} construct is relaxed to expression to 
allow initializers at declaration time.  */

  syntax Exp ::= DeclId 
               | PointerId
  syntax DeclId ::= int Exp [prec 40] 
  syntax PointerId ::= Id 
                     | * PointerId [prec 25 strict]

/*@ \subsection{Memory allocation and addressing}
Again, for simplicity  we spell out a fixed syntax for malloc, using the 
size of integers as a multiplication factor and the result to an integer 
pointer.  */

  syntax Exp ::=  `NULL
               | * Exp [ditto]
               | Exp [ Exp ] [prec 0]
               | ( int * ) malloc ( Exp * sizeof ( int ) ) [strict] 
               | free ( Exp ) [strict] 

/*@ \subsection{Assignment}
We have {\it Exp} in the left side to allow assigning to both variables 
and heap locations.  */

  syntax Exp ::= Exp = Exp [strict(2) prec 40 gather (e E)] 

//@ \subsection{User-declared Functions}

/*@ \subsubsection{Function declaration}
A function declaration consists of a {\it DeclId}, that is, a typed 
identifier, followed by a list of {\it DeclId}s (which should be 
surrounded by parentheses, although not required), and then by the body 
of the function. */

  syntax Stmt ::= DeclId List{DeclId} { StmtList }
  syntax DeclId ::= void PointerId [prec 40]

//@ \subsubsection{Function invocation and return}

  syntax Exp ::= Id ( List{Exp} ) [prec 0 strict(2)] 
               | Id ( ) [prec 0]
  syntax Stmt ::= return Exp ; [strict]

/*@ As our current parser is ``algebraic'', the empty list needs to be 
identifiable as a constant (unlike CFG grammars, where it can simply be 
the empty string/epsilon production). Therefore, if only using the first 
syntactic production for function invocation, one would need to 
explicitly specify the empty list constant for calling a function with 
zero arguments. To avoid having to do that, we add a separate production 
with explicitly no arguments; this is desugared into the first one in the 
{\tt KERNELC-DESUGARED-SYNTAX} module.  */

//@ \subsection{Statements}

  syntax Stmt ::= { } 
                | { StmtList } 
                | Exp ; [prec 45 strict] 
                | if ( Exp ) Stmt [prec 47]
                | if ( Exp ) Stmt else Stmt [prec 46 strict(1)]
                | while ( Exp ) Stmt 

  syntax StmtList ::= Stmt 
                    | StmtList StmtList [prec 100 gather (e E)]



/*@ \subsection{\#include pragmas}
To allow splitting programs into fragments (statement lists) which are 
then included one in another and to facilitate code reuse we introduce 
the use of {\tt \#include} preprocessing commands.  */

  syntax StmtList ::= #include < CompilationUnit >
  syntax CompilationUnit ::= stdio.h | stdlib.h

/*@ The above constants are introduced so that \KERNELC accepts a larger 
subset of the C programs (refering to standard functions). */

//@ \subsection{Program and the main function}

  syntax Pgm ::= StmtList 

  syntax Id ::= main

//@ \subsection{Additional Library Functions}

/*@ \subsubsection{Input/Output}
For simplicity we syntactically restrict the {\tt printf} and 
{\tt scanf} to have only one, identifiable, argument.  
As the \& operator is not part of the language, we opt for two versions 
of {\tt scanf}, first for reading (local) variables, e.g., 
\verb#scanf("%d",&x)#, and the other for reading into the heap location 
to which the argument evaluates to.  */ 

  syntax Exp ::= printf ( "%d;" , Exp ) [strict] 
               | scanf ( "%d" , & Exp )
               | scanf ( "%d" , Exp ) [strict] 

/*@ \subsubsection{Random}
The following functions are defined in the standard {\tt stdlib.h} header 
and provide a pseudo-random number generator.  {\tt srand} is used to 
initialize the seed, while rand returns a pseudo-random 32-bits number. */

  syntax Exp ::= srand ( Exp ) [strict]
               | rand ( ) 

  /*@ \subsection{Lists}
Currently we have to explicitly declare the syntactic lists (they will be
eventually builtin). Note that they are associative, strict and hybrid, 
which means that once they reach the top of the computation each of their 
elements is evaluated to a result and the obtained list of results is 
automatically considered to be a result.  */

  sort Bottom 
  syntax List{Bottom} ::= () | Bottom | List{Bottom} , List{Bottom}  [assoc id: () strict hybrid prec 45]
  syntax List{PointerId} ::= PointerId | List{Bottom} | List{PointerId} , List{PointerId} [ditto]
  syntax List{DeclId} ::= DeclId | List{Bottom} | List{DeclId} , List{DeclId} [ditto]
  syntax List{Exp} ::= Exp | List{PointerId} | List{DeclId} |  List{Exp} , List{Exp} [ditto]
endkm

kmod KERNELC-DESUGARED-SYNTAX is including KERNELC-SYNTAX 

/*@ \section{Desugaring}    
Expressing some constructs in terms of others to reduce the amount of 
constructs to which semantics needs to be given. */

/*@ {\bf Logical operators} are desugared into instances of the 
conditional expression, thus also ensuring a shortcut semantics for 
them. */

  macro ! E:Exp = E ? 0 : 1
  macro E1:Exp && E2:Exp = E1 ? E2 : 0
  macro E1 || E2 = E1 ? 1 : E2
 
  macro if(E) St:Stmt = if(E) St else {}
  macro NULL = 0

/*@ {\bf Calling a function with zero arguments} is desugared in the 
normal call with the empty list `()' as argument. */

  macro I:Id () = I (())

/*@ {\bf Standard header inclusion} is ignored, as we give direct 
semantics for the supported functions. */

  macro #include<stdio.h> = {}
  macro #include<stdlib.h> = {}

//@ {\bf Array access} is pointer dereference

  macro E1[E2] = *(E1 + E2)

//@ {\bf Simplifying ``{\tt \& * E}''} in the context of {\tt scanf}

  macro scanf( "%d" , & * E) = scanf("%d", E)

/*@ {\bf Flattening types.} As currently we don't perform any type 
checking, either static or dynamic, we here forget typing information 
for variable declarations. */

  macro int * PointerId:PointerId = int PointerId
  macro (int * PointerId = E) = (int PointerId = E)

/*@ {\bf Declaration with initialization} is desugared into the two
composing operations. */

  macro (int X:Id = E ;) = int X ; X = E ;
endkm





