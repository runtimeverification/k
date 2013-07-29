/*
require "../../basic/cink-basic-syntax.k"
require "../../basic/cink-basic-semantics.k"
require "../../l-r-values/cink-l-r-values.k"
*/
require "../../pointers/cink-pointers.k"

module CINK-ARRAYS-SYNTAX

  syntax Exp ::= Exp "[" Exp "]" [strict, array]
               | Exp "[]" [array] 

  syntax priorities  array > multiply read write greatthan lessequal
  syntax priority  array > assign

endmodule

module CINK-ARRAYS-SEMANTICS

  imports CINK-BASIC-SEMANTICS
  imports CINK-POINTERS-SEMANTICS
  imports CINK-ARRAYS-SYNTAX
  imports ARRAY

  /* From C++ 2011 Manual:
  \begin{quote}
  In a declaration T D where D has the form\\
   \indent   D1 [ constant-expressionopt] attribute-specifier-seqopt\\
   and the type of the identifier in the declaration T D1 is 
   "derived-declarator-type-list T", then the type of the identifier of D
   is an array type...\\
   Example:
   \begin{verbatim}
      typedef int A[5], AA[2][3];
      typedef const A CA; // type is "array of 5 const int"
      typedef const AA CAA; // type is "array of 2 array of 3 const int"
  \end{verbatim}
  \ldots\\
   An array can be constructed from one of the fundamental types (except void),
   from a pointer, from a pointer to member, from a class, from an enumeration
   type, or from another array.\\
   When several "array of" specifications are adjacent, a multidimensional array
   is created; only the first of the constant expressions that specify the 
   bounds of the arrays may be omitted. In addition to declarations in
   which an incomplete object type is allowed, an array bound may be omitted in
   some cases in the declaration of a function parameter (8.3.5). An array 
   bound may also be omitted when the declarator is followed by an
   initializer (8.5). In this case the bound is calculated from the number of 
   initial elements (say, N) supplied (8.5.1), and the type of the identifier
   of D is "array of N T.
   \end{quote}
  */

  /*@
  First we define array types following the the notation convention from
  the manual. 
  We call these type \emph{explicit array types}. Note that these have a 
  recursive definition.  
  We also extends statements with declaration of variable (expression)
  of the new type.
  */

  syntax ArrType ::= "array" "of" Int Type 
  syntax Type ::= ArrType
  syntax Stmt ::= Exp "of" ArrType ";"

  /*@
  The arrays are locations storing locations:
  */
  syntax Loc ::= Array


  /*@
  The array declaration are translated into declaration with explicit array
  types.
  */

  rule T:Type X:Exp[N:Int]; => X of array of N T;

  /*@
  An array \texttt{a[3]} will be represented as follows:
  \begin{verbatim}
  <env>
    a |-> #symLoc(2)
  </env>
  <store>
    #symLoc(2) |-> store(store(store(const-array(3, undefined),
                               0, #symLoc(3)),
                               1, #symLoc(4))
                               2, #symLoc(5))
        #symLoc(3) |-> undefined
        #symLoc(4) |-> undefined
        #symLoc(5) |-> undefined
    </store>
  \end{verbatim}
  We use an auxiliary function for allocating locations for members:
  */

  syntax K ::= "alloc" "(" Stmt "," Int ")" 

  /*@
  The initial call:
  */
  rule <k> X:Id of array of N:Int T:Type;
           =>
           alloc(X of array of N T;, 0)
       ...</k>
       <env>... . => X |-> L </env>
       <store>... . => L |-> const-array(N, undefined) </store>
       when fresh(L:Loc)

  /*@
  The recursive case:
  */
  rule <k> alloc(X:Exp of array of N:Int T:Type;, I:Int)
           =>
           alloc(X of array of N T;, I +Int 1)
       ...</k>
       <env>... X |-> L (. => X[I] |-> L') </env>
       <store>...
              (L |-> (A:Array => store(A, I, L')))
              (. =>  L' |-> undefined)
       ...</store>
       when fresh(L':Loc) andBool (I <Int N)

  /*@
   The base case when all components given by the current index
  are allocated:
  */ 
  rule alloc(X:Exp of array of N:Int AT:Type;, I:Int) => .
       when (I >=Int N)

  /*@
  The evaluation of an array component as an rvalue:
  */
  rule A:Array [I:Int] => * (A + I)

  rule A:Array + I:Int => select(A, I) 

  context _:Exp[HOLE] = _


  /*@
  The evaluation of an array component as an lvalue:
  */
  context lvalue(_:Exp[HOLE])

  context lvalue((HOLE => lvalue(HOLE))[_:Exp])

  rule <k> lvalue(L:Loc[I:Int] => select(A, I) ) ...</k>
       <store>... L |-> A:Array ...</store>

  rule lvalue(A:Array + I:Int) =>  select(A,I) ~> lvalue(HOLE)
  rule L:Loc ~> lvalue(HOLE) => lvalue(& L)

  /*@ 
  Arrays as parameters:
  */

  context evaluate ((HOLE => lvalue(HOLE)), _:Exps) to _:Vals
          following (T _:Exp[_:Exp], _:Decls);

  context evaluate ((HOLE => lvalue(HOLE)), _:Exps) to _:Vals
          following (T _:Exp[], _:Decls);

  rule <k>
          bind((L:LVal, Vs:Vals) => Vs) to((T X:Id[], Xl:Decls) => Xl); 
       ...</k>
       <env> Env:Map => Env[L/X] </env>
       [structural]


endmodule

