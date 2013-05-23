require "cink-basic-syntax.k"
require "cink-basic-semantics.k"
require "cink-l-r-values.k"


module CINK-INCR-DECR-SEMANTICS

  imports CINK-BASIC-SEMANTICS
  imports CINK-L-R-VALUES-SEMANTICS

  // for transforming the lvalue into a rvalue

  syntax Exp ::= "rvalue" "(" Exp ")"

  rule <k>  rvalue(L:Loc) => V ...</k>
       <store>... L |-> V ...</store>

  // heating & cooling rules for assignment
  rule E1:Exp = E2:Exp => E2 ~> E1 = HOLE [heat]

  rule V:Val ~> E:Exp = HOLE => seqpoint ~> E = V  [cool]

  rule L:Loc ~> E:Exp = HOLE => seqpoint ~> E = rvalue(L) [cool]

  // heating & cooling rules for plus
  rule E1:Exp + E2:Exp => E1 ~> HOLE + E2 [heat]

  rule E1:Exp + E2:Exp => E2 ~> E1 + HOLE [heat]

  rule V:Val ~> HOLE + E:Exp => V + E  [cool]

  rule V:Val ~> E:Exp + HOLE => E + V  [cool]

  rule L:Loc ~> HOLE + E:Exp => rvalue(L) + E [cool]

  rule L:Loc ~> E:Exp + HOLE => E + rvalue(L) [cool]

  // heating & cooling rules for minus
  rule E1:Exp - E2:Exp => E1 ~> HOLE - E2 [heat]

  rule E1:Exp - E2:Exp => E2 ~> E1 - HOLE [heat]

  rule V:Val ~> HOLE - E:Exp => V - E  [cool]

  rule V:Val ~> E:Exp - HOLE => E - V  [cool]

  rule L:Loc ~> HOLE - E:Exp => rvalue(L) - E [cool]

  rule L:Loc ~> E:Exp - HOLE => E - rvalue(L) [cool]

  // heating & cooling rules for multiply
  rule E1:Exp * E2:Exp => E1 ~> HOLE * E2 [heat]

  rule E1:Exp * E2:Exp => E2 ~> E1 * HOLE [heat]

  rule V:Val ~> HOLE * E:Exp => V * E  [cool]

  rule V:Val ~> E:Exp * HOLE => E * V  [cool]

  rule L:Loc ~> HOLE * E:Exp => rvalue(L) * E [cool]

  rule L:Loc ~> E:Exp * HOLE => E * rvalue(L) [cool]

  // heating & cooling rules for divide
  rule E1:Exp / E2:Exp => E1 ~> HOLE / E2 [heat]

  rule E1:Exp / E2:Exp => E2 ~> E1 / HOLE [heat]

  rule V:Val ~> HOLE / E:Exp => V / E  [cool]

  rule V:Val ~> E:Exp / HOLE => E / V  [cool]

  rule L:Loc ~> HOLE / E:Exp => rvalue(L) / E [cool]

  rule L:Loc ~> E:Exp / HOLE => E / rvalue(L) [cool]

  // heating & cooling rules for rest-modulo
  rule E1:Exp % E2:Exp => E1 ~> HOLE % E2 [heat]

  rule E1:Exp % E2:Exp => E2 ~> E1 % HOLE [heat]

  rule V:Val ~> HOLE % E:Exp => V % E  [cool]

  rule V:Val ~> E:Exp % HOLE => E % V  [cool]

  rule L:Loc ~> HOLE % E:Exp => rvalue(L) % E [cool]

  rule L:Loc ~> E:Exp % HOLE => E % rvalue(L) [cool]

  // heating & cooling rules for less than
  rule E1:Exp < E2:Exp => E1 ~> HOLE < E2 [heat]

  rule E1:Exp < E2:Exp => E2 ~> E1 < HOLE [heat]

  rule V:Val ~> HOLE < E:Exp => V < E  [cool]

  rule V:Val ~> E:Exp < HOLE => E < V  [cool]

  rule L:Loc ~> HOLE < E:Exp => rvalue(L) < E [cool]

  rule L:Loc ~> E:Exp < HOLE => E < rvalue(L) [cool]

  // heating & cooling rules for less than or equal to
  rule E1:Exp <= E2:Exp => E1 ~> HOLE <= E2 [heat]

  rule E1:Exp <= E2:Exp => E2 ~> E1 <= HOLE [heat]

  rule V:Val ~> HOLE <= E:Exp => V <= E  [cool]

  rule V:Val ~> E:Exp <= HOLE => E <= V  [cool]

  rule L:Loc ~> HOLE <= E:Exp => rvalue(L) <= E [cool]

  rule L:Loc ~> E:Exp <= HOLE => E <= rvalue(L) [cool]

  // heating & cooling rules for greater than
  rule E1:Exp > E2:Exp => E1 ~> HOLE > E2 [heat]

  rule E1:Exp > E2:Exp => E2 ~> E1 > HOLE [heat]

  rule V:Val ~> HOLE > E:Exp => V > E  [cool]

  rule V:Val ~> E:Exp > HOLE => E > V  [cool]

  rule L:Loc ~> HOLE > E:Exp => rvalue(L) > E [cool]

  rule L:Loc ~> E:Exp > HOLE => E > rvalue(L) [cool]

  // heating & cooling rules for equality
  rule E1:Exp == E2:Exp => E1 ~> HOLE == E2 [heat]

  rule E1:Exp == E2:Exp => E2 ~> E1 == HOLE [heat]

  rule V:Val ~> HOLE == E:Exp => V == E  [cool]

  rule V:Val ~> E:Exp == HOLE => E == V  [cool]

  rule L:Loc ~> HOLE == E:Exp => rvalue(L) == E [cool]

  rule L:Loc ~> E:Exp == HOLE => E == rvalue(L) [cool]


  /*@ \subsubsection{The prefix increment operator}
    Here is the description of this operator from the manual of 
    \Cpp 2011 (5.3.2):\\
    "The operand of prefix ++ is modified by adding 1, or set to true 
    if it is bool (this use is deprecated). The operand shall be a 
    modifiable lvalue. The type of the operand shall be an arithmetic 
    type or a pointer to a completely-defined object type. 
    The result is the updated operand; it is an lvalue, and it is a 
    bit-field if the operand is a bit-field."\\
    This definition raises some problems.
    We suppose that we want to evaluate the
    expression \texttt{y + (++x)}; since the addition operator is strict in 
    both arguments, it will be reduced something like $\it I + lL$ and 
    in that case $L$ should be evaluated to the value stored into
    the location $L$. On the other hands, the evaluation of the expression
    \texttt{++ (++x)} uses the l-value returned by the operator.
    This is one reason for that we make a clear distinction
    between r-value and l-value expressions and use the contexts declarations
    in order to specify how to valuate subexpressions.
  */

  // heating the argument of the prefix increment as an lvalue
  context ++ (HOLE => lvalue(HOLE))

 // for nested increment expressions:

  rule lvalue(++ E:Exp) => ++ E:Exp ~> lvalue(HOLE) [heat]
  rule L:Loc ~> lvalue(HOLE) => lvalue(L) [cool]

  // the semantics of the the prefix increment
  rule <k> ++ L:Loc => L ...</k>
       <store>... L |-> (V:Int => V +Int 1) ...</store>


  /*@
  \subsubsection{The postfix increment operator}
   Here is the description of this operator from the manual of 
  \Cpp 2011 (5.2.6):
  "The value of a postfix ++ expression is the value of its operand.
  [ Note: the value obtained is a copy of
  the original value —end note ] The operand shall be a modifiable lvalue.
  The type of the operand shall be an arithmetic type or a pointer to a
  complete object type. The value of the operand object is modified by
  adding 1 to it, unless the object is of type bool, in which case it is set
  to true. [ Note: this use is deprecated, see Annex D. —end note ]
  The value computation of the ++ expression is sequenced before the
  modification of the operand object. With respect to an 
  indeterminately-sequenced function call, the operation of postfix
  ++ is a single evaluation.
  [ Note: Therefore, a function call shall not intervene between the
  lvalue-to-rvalue conversion and the side effect associated with any single
  postfix ++ operator. —end note ] The result is a prvalue."
  From the Appendix D: \\
  "D.1 The use of an operand of type bool with the ++ operator is deprecated 
  (see 5.3.2 and 5.2.6)."
  */

  configuration 
     <sideEffects> .K </sideEffects>

  syntax K ::= "$inc" "(" K ")" | "$dec" "(" K ")" | "seqpoint"

  context (HOLE => lvalue(HOLE)) ++

  rule <k> L:Loc ++ => V ...</k>
       <store>... L |-> V:Int ...</store>
       <sideEffects> . => $inc(L) ...</sideEffects>


  rule <k> seqpoint => SE ...</k>
       <sideEffects> SE => . </sideEffects>


  rule <k> $inc(L:Loc) => . ...</k>
       <store>... L |-> (V:Int => V +Int 1) ...</store>


  rule <k> $dec(L:Loc) => . ...</k>
       <store>... L |-> (V:Int => V -Int 1) ...</store>

 

endmodule
