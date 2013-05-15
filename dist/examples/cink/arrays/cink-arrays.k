require "../basic/cink-basic.k"

module CINK-ARRAYS-SYNTAX

  syntax Exp ::= Exp "[" Exp "]" [strict, array]

  syntax priorities  array > read write greatthan lessequal
  syntax priority  array > assign


endmodule

module CINK-ARRAYS-SEMANTICS

  imports CINK-BASIC-SEMANTICS
  imports CINK-ARRAYS-SYNTAX
  imports ARRAY

  /* From C++ 2011 Manual:\\
  "In a declaration T D where D has the form\\
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
  ... 
  "An array can be constructed from one of the fundamental types (except void),
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
   of D is "array of N T."
  */

  syntax ArrRecType ::= "array" "of" Int Type | "array" "of" Int ArrRecType
  syntax Stmt ::= Exp "of" ArrRecType ";"

//  syntax Id ::= "Id" "(" Exp ")"

  rule T:Type X:Exp[N:Int]; => X of array of N T;

  rule X:Exp[N:Int] of ART:ArrRecType; => X of array of N ART;

  syntax Val ::= "array" "(" K "," Int "," K ")" | Array 

  syntax K ::= "alloc" "(" Stmt "," Int ")" 

  rule <k>
          X:Id of array of N:Int ART:ArrRecType;
          =>
          alloc(X of array of N ART;, 0)
       ...</k>
 
  rule <k> alloc(X:Exp of array of N:Int ART:ArrRecType;, I:Int)
           =>
           alloc(X[I] of ART;, 0) ~>
           alloc(X of array of N ART;, I +Int 1)
       ...</k>
       when (I <Int N)

  rule <k> alloc(X:Exp of array of N:Int ART:ArrRecType;, I:Int) => . ...</k>
       <env>... . => X |-> L </env>
       <store>... . => L |-> array(X, N, array of N ART) </store>
       when fresh(L:Loc) andBool (I >=Int N)

  rule <k> alloc(X:Exp of array of N:Int T:Type;, I:Int)
           =>
           .
       ...</k>
       <env>... . => X |-> L </env>
       <store>... . => L |-> const-array(X, 0, N, undefined) </store>
       when fresh(L:Loc) andBool (I <Int N)

//  context _:Exp[HOLE] = _
  
  syntax K ::= "lvalue" "(" K ")"

  syntax Val ::= Loc 
  syntax Loc ::=  "locElem" "(" K ")"

  context (HOLE => lvalue(HOLE)) = _:Exp

  rule <k> lvalue(X:Id => L) ...</k>
       <env>... X |-> L:Loc ...</env>

  rule <k> lvalue(L:Loc[I:Int] => L' ) ...</k>
       <env>... X:Exp |-> L  X[I] |-> L':Loc ...</env>

  rule <k> lvalue(L:Loc[I:Int] => locElem(L[I])) ...</k>
       <store>... L |-> _:Array ...</store>

  context lvalue(_:Exp[HOLE])
  context lvalue((HOLE => lvalue(HOLE))[_:Exp])


  rule <k> lvalue(X:Id => L) ...</k>
       <env>... X |-> L:Loc ...</env>

  rule <k> L:Loc = V:Val  => V ...</k>/
       <store>... L |-> (_ => V) ...</store>

  rule <k> locElem(L:Loc[I:Int]) = V:Val  => V ...</k>
       <store>... L |-> (A:Array => store(A, I, V)) ...</store>


  rule A:Array [I:Int] => select(A, I)

  rule <k> array(X:Exp, _:Int, _:K)[I:Int] => Y ...</k>
       <env>... X[I] |-> L:Loc ...</env>
       <store>... L |-> Y:K ...</store>

  context cin >> (HOLE => lvalue(HOLE))

  rule <k> cin >> L:Loc => cin  ...</k>
       <store>... L |-> (_ => V)  ...</store>
       <in> (ListItem(V:Int) => .)  ...</in>
       [read-stream]

  rule <k> cin >> locElem(L:Loc[I:Int]) => cin  ...</k>
       <store>... L |-> (A:Array => store(A, I, V))  ...</store>
       <in> (ListItem(V:Int) => .)  ...</in>
       [read-stream]

endmodule

