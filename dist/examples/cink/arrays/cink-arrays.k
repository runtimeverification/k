require "../l-r-values/cink-l-r-values.k"

module CINK-ARRAYS-SYNTAX

  syntax Exp ::= Exp "[" Exp "]" [strict, array]

  syntax priorities  array > read write greatthan lessequal
  syntax priority  array > assign


endmodule

module CINK-ARRAYS-SEMANTICS

  imports CINK-L-R-VALUES-SYNTAX
  imports CINK-ARRAYS-SYNTAX
  imports CINK-BASIC-SEMANTICS
  imports CINK-L-R-VALUES-SEMANTICS
  imports ARRAY

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
  The array declaration are translated into declaration with explicit array
  types.
  */

  rule T:Type X:Exp[N:Int]; => X of array of N T;

  rule X:Exp[N:Int] of AT:ArrType; => X of array of N AT;

  /*@
  We need declare the arrays as values: .
  */

  syntax Val ::= Array 

  /*@
  An array \texttt{a[2][3]} will be represented as follows:
  \begin{verbatim}
  <env>
    a[0] |-> #symLoc(3)
    a[1] |-> #symLoc(4)
    a |-> #symLoc(2)
  </env>
  <store>
    #symLoc(2) |-> store(store(const-array(a, 0, 2, undefined),
                               0, #symLoc(3)),
                         1, #symLoc(4))
        #symLoc(3) |-> const-array(a[0], 0, 2, undefined )
        #symLoc(4) |-> const-array(a[1], 0, 2, undefined )
    </store>
  \end{verbatim}
  Since the definition of the multidimensional array is recursive, the 
  allocation is described by a recursive function:
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
       <store>... . => L |-> const-array(X, 0, N, undefined) </store>
       when fresh(L:Loc)

  /*@
  The recursive case, when $X$ denotes a $N$-dimensional array with $N\ge 2$:
  */
  rule <k> alloc(X:Exp of array of N:Int array of N':Int T:Type;, I:Int)
           =>
           alloc(X[I] of array of N' T;, 0) ~>
           alloc(X of array of N array of N':Int T;, I +Int 1)
       ...</k>
       <env>... X |-> L (. => X[I] |-> L') </env>
       <store>...
              (L |-> (A:Array => store(A, I, L')))
              (. =>  L' |-> const-array(X[I], 0, N', undefined))
       ...</store>
       when fresh(L':Loc) andBool (I <Int N)

  /*@
   The base case when all components given by the current index
  are allocated:
  */ 
  rule alloc(X:Exp of array of N:Int AT:ArrType;, I:Int) => .
       when fresh(L:Loc) andBool (I >=Int N)

  /*@
   The base case when X denotes a unidimensional array:
  */ 
  rule <k> alloc(X:Exp of array of N:Int T:Type;, I:Int)
           =>
           .
       ...</k>
       when fresh(L:Loc) andBool isArrType(T) =/=K true

  /*@
  We introduce a new constructor for locations, corresponding to a component
  of unidimensional array of basic types:
  */
  syntax Loc ::=  "locElem" "(" K ")"

  /*@
  The evaluation of an array component as a lvalue:
  */
  context lvalue(_:Exp[HOLE])

  context lvalue((HOLE => lvalue(HOLE))[_:Exp])

  rule <k> lvalue(L:Loc[I:Int] => L' ) ...</k>
       <env>... X:Exp |-> L  X[I] |-> L':Loc ...</env>

  rule <k> lvalue(L:Loc[I:Int] => locElem(L[I])) ...</k>
       <env> X:Exp |-> L Env:Map </env>
       <store>... L |-> _:Array ...</store>
       when notBool $hasMapping(Env, X[I])


  /*@
  The evaluation of an array component as a lvalue:
  */
  rule <k> locElem(L:Loc[I:Int]) = V:Val  => V ...</k>
       <store>... L |-> (A:Array => store(A, I, V)) ...</store>

  rule A:Array [I:Int] => select(A, I)

  rule <k> L:Loc [I:Int] => select(A, I) ...</k>
       <store>... L |-> A:Array ...</store>

  /*@
  The semantics operator for a component of an array requires a new rule,
  because the location of the component does not explicitly appear in the store:
  */
  rule <k> cin >> locElem(L:Loc[I:Int]) => cin  ...</k>
       <store>... L |-> (A:Array => store(A, I, V))  ...</store>
       <in> (ListItem(V:Int) => .)  ...</in>
       [read-stream]

endmodule

