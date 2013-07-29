// require "../l-r-values/cink-l-r-values.k"
 require "../pointers/cink-pointers.k"

module CINK-ARRAYS-SYNTAX

  syntax Exp ::= Exp "[" Exp "]" [strict, array]
               | Exp "[]" [array] 

  syntax priorities  array > multiply read write greatthan lessequal
  syntax priority  array > assign

endmodule

module CINK-ARRAYS-SEMANTICS

  imports CINK-ARRAYS-SYNTAX
  imports CINK-BASIC-SEMANTICS
  imports CINK-POINTERS-SEMANTICS
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
  The arrays are locations storing locations:
  */
  syntax Loc ::= Array

  /*@
  An array \texttt{a[2][3]} will be represented as follows:
  \begin{verbatim}
  <env>
    a[0] |-> #symLoc(3)
    a[1] |-> #symLoc(7)
    a |-> #symLoc(2)
  </env>
  <store>
    #symLoc(2) |-> store(store(const-array(3, undefined),
                               0, #symLoc(3)),
                               1, #symLoc(4))
        #symLoc(3) |-> store(store(store(const-array(3, undefined),
                               0, #symLoc(4)),
                               0, #symLoc(5)),
                               1, #symLoc(6))
        #symLoc(4) |-> undefined
        #symLoc(5) |-> undefined
        #symLoc(6) |-> undefined
        #symLoc(7) |-> store(store(store(const-array(3, undefined),
                               0, #symLoc(8)),
                               0, #symLoc(9)),
                               1, #symLoc(10))
        #symLoc(8) |-> undefined
        #symLoc(9) |-> undefined
        #symLoc(10) |-> undefined
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
       <store>... . => L |-> const-array(N, undefined) </store>
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
              (. =>  L' |-> const-array(N', undefined))
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
           alloc(X of array of N T;, I +Int 1)
       ...</k>
       <env>... X |-> L (. => X[I] |-> L') </env>
       <store>...
              (L |-> (A:Array => store(A, I, L')))
              (. =>  L' |-> undefined)
       ...</store>
       when fresh(L':Loc) andBool (isArrType(T) =/=K true) andBool (I <Int N)

  /*@
   The base case when all components of the current unidimensional array 
  are allocated:
  */ 

  rule <k> alloc(X:Exp of array of N:Int T:Type;, I:Int)
           =>
           .
       ...</k>
       when fresh(L:Loc)  andBool (I >=Int N) andBool isArrType(T) =/=K true


  /*@
  The evaluation of an array component as a lvalue:
  */

  context lvalue(_:Exp[HOLE])

  context lvalue((HOLE => lvalue(HOLE))[_:Exp])

  rule <k> lvalue(L:Loc[I:Int] => L' ) ...</k>
       <env>... X:Exp |-> L  X[I] |-> L':Loc ...</env>

  rule lvalue(A:Array + I:Int) =>  select(A,I) ~> lvalue(HOLE)
  rule L:Loc ~> lvalue(HOLE) => lvalue(& L)

  /*@
  The evaluation of an array component as an rvalue:
  */

  rule A:Array [I:Int] => * (A + I)

  rule A:Array + I:Int => select(A, I) 

  context _:Exp[HOLE] = _


  /*@ 
  Arrays as parameters:
  */

  context evaluate ((HOLE => lvalue(HOLE)), _:Exps) to _:Vals
          following (T _:Exp[], _:Decls);

  context evaluate ((HOLE => lvalue(HOLE)), _:Exps) to _:Vals
          following (T _:Exp[_:Exp], _:Decls);

  rule <k>
          bind((L:LVal, Vs:Vals) => Vs) to((T X:Id[], Xl:Decls) => Xl); 
       ...</k>
       <env> Env:Map => Env[L/X] </env>
       [structural]

  rule bind(L:LVal, Vs:Vals) to (T X:Exp[_:Exp], Xl:Decls); 
       =>
       bind(L:LVal, Vs:Vals) to (T X, Xl:Decls); 
       [structural]

  rule bind(L:LVal, Vs:Vals) to (T X:Exp[][], Xl:Decls); 
       =>
       bind(L:LVal, Vs:Vals) to (T X[], Xl:Decls); 
       [structural]

endmodule

