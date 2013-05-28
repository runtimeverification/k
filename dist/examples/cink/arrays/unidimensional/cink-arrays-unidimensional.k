require "../../basic/cink-basic.k"

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

  rule <k> T:Type X:Id[N:Int] ; => . ...</k>
       <env>... . => X |-> L </env>
       <store>... . => L |-> const-array(N, undefined) </store>
       when fresh(L:Loc)

  syntax Val ::= Array

  rule A:Array [I:Int] => select(A, I) 

  context _:Exp[HOLE] = _

  rule <k> X:Id[I:Int] = V:Int => V ...</k>
       <env>... X |-> L:Loc ...</env>
       <store>... L |-> (A:Array => store(A, I, V)) ...</store>

  context cin >> X:Exp[HOLE]

  rule <k> cin >> X:Id[I:Int] => cin  ...</k>
       <env>...  X |-> L:Loc  ...</env>
       <store>... L |-> (A:Array => store(A, I, V))  ...</store>
       <in> (ListItem(V:Int) => .)  ...</in>
       [read-stream]

endmodule

