require "cink-basic-syntax.k"
require "cink-basic-semantics.k"
require "cink-l-r-values.k"


module CINK-INCR-DECR-SEMANTICS

  imports CINK-BASIC-SEMANTICS
  imports CINK-L-R-VALUES-SEMANTICS

  /*@
   There are cases when an lvalue must be converted into its rvalue.
   For instance x++ + y will be evaluated to lvalue-of-x + rvalue-of-y.
   Obviously, lvalue-of-x must be converted into rvalue-of-x in this
   context.\\
   Therefore we extend expressions with a "rvalue" wrapper, similar to
   "lvalue".
  */ 

  syntax Exp ::= "rvalue" "(" Exp ")"

  /*@
   The rule realizing the conversion is very simple: it replaces the
   expresion with the value stored at the location given as paraemeter.
  */

  rule <k>  rvalue(L:Loc) => V ...</k>
       <store>... L |-> V ...</store>

  /*@ since the cooling rules for the arithmetic and logic operators depend
    on the type of the result, i.e. whether it is an lvalue or a rvalue, 
    we have to disable the strict attribute and manually write the heating
    and cooling rules.
  */

  // heating & cooling rules for assignment
  rule E1:Exp = E2:Exp => E2 ~> E1 = HOLE [heat]

  rule V:RVal ~> E:Exp = HOLE => seqpoint ~> E = V  [cool]

  rule L:Loc ~> E:Exp = HOLE => seqpoint ~> E = rvalue(L) [cool]

  // heating & cooling rules for plus
  rule E1:Exp + E2:Exp => E1 ~> HOLE + E2 [heat]

  rule E1:Exp + E2:Exp => E2 ~> E1 + HOLE [heat]

  rule V:RVal ~> HOLE + E:Exp => V + E  [cool]

  rule V:RVal ~> E:Exp + HOLE => E + V  [cool]

  rule L:Loc ~> HOLE + E:Exp => rvalue(L) + E [cool]

  rule L:Loc ~> E:Exp + HOLE => E + rvalue(L) [cool]

  // heating & cooling rules for minus
  rule E1:Exp - E2:Exp => E1 ~> HOLE - E2 [heat]

  rule E1:Exp - E2:Exp => E2 ~> E1 - HOLE [heat]

  rule V:RVal ~> HOLE - E:Exp => V - E  [cool]

  rule V:RVal ~> E:Exp - HOLE => E - V  [cool]

  rule L:Loc ~> HOLE - E:Exp => rvalue(L) - E [cool]

  rule L:Loc ~> E:Exp - HOLE => E - rvalue(L) [cool]

  // heating & cooling rules for multiply
  rule E1:Exp * E2:Exp => E1 ~> HOLE * E2 [heat]

  rule E1:Exp * E2:Exp => E2 ~> E1 * HOLE [heat]

  rule V:RVal ~> HOLE * E:Exp => V * E  [cool]

  rule V:RVal ~> E:Exp * HOLE => E * V  [cool]

  rule L:Loc ~> HOLE * E:Exp => rvalue(L) * E [cool]

  rule L:Loc ~> E:Exp * HOLE => E * rvalue(L) [cool]

  // heating & cooling rules for divide
  rule E1:Exp / E2:Exp => E1 ~> HOLE / E2 [heat]

  rule E1:Exp / E2:Exp => E2 ~> E1 / HOLE [heat]

  rule V:RVal ~> HOLE / E:Exp => V / E  [cool]

  rule V:RVal ~> E:Exp / HOLE => E / V  [cool]

  rule L:Loc ~> HOLE / E:Exp => rvalue(L) / E [cool]

  rule L:Loc ~> E:Exp / HOLE => E / rvalue(L) [cool]

  // heating & cooling rules for rest-modulo
  rule E1:Exp % E2:Exp => E1 ~> HOLE % E2 [heat]

  rule E1:Exp % E2:Exp => E2 ~> E1 % HOLE [heat]

  rule V:RVal ~> HOLE % E:Exp => V % E  [cool]

  rule V:RVal ~> E:Exp % HOLE => E % V  [cool]

  rule L:Loc ~> HOLE % E:Exp => rvalue(L) % E [cool]

  rule L:Loc ~> E:Exp % HOLE => E % rvalue(L) [cool]

  // heating & cooling rules for less than
  rule E1:Exp < E2:Exp => E1 ~> HOLE < E2 [heat]

  rule E1:Exp < E2:Exp => E2 ~> E1 < HOLE [heat]

  rule V:RVal ~> HOLE < E:Exp => V < E  [cool]

  rule V:RVal ~> E:Exp < HOLE => E < V  [cool]

  rule L:Loc ~> HOLE < E:Exp => rvalue(L) < E [cool]

  rule L:Loc ~> E:Exp < HOLE => E < rvalue(L) [cool]

  // heating & cooling rules for less than or equal to
  rule E1:Exp <= E2:Exp => E1 ~> HOLE <= E2 [heat]

  rule E1:Exp <= E2:Exp => E2 ~> E1 <= HOLE [heat]

  rule V:RVal ~> HOLE <= E:Exp => V <= E  [cool]

  rule V:RVal ~> E:Exp <= HOLE => E <= V  [cool]

  rule L:Loc ~> HOLE <= E:Exp => rvalue(L) <= E [cool]

  rule L:Loc ~> E:Exp <= HOLE => E <= rvalue(L) [cool]

  // heating & cooling rules for greater than
  rule E1:Exp > E2:Exp => E1 ~> HOLE > E2 [heat]

  rule E1:Exp > E2:Exp => E2 ~> E1 > HOLE [heat]

  rule V:RVal ~> HOLE > E:Exp => V > E  [cool]

  rule V:RVal ~> E:Exp > HOLE => E > V  [cool]

  rule L:Loc ~> HOLE > E:Exp => rvalue(L) > E [cool]

  rule L:Loc ~> E:Exp > HOLE => E > rvalue(L) [cool]

  // heating & cooling rules for equality
  rule E1:Exp == E2:Exp => E1 ~> HOLE == E2 [heat]

  rule E1:Exp == E2:Exp => E2 ~> E1 == HOLE [heat]

  rule V:RVal ~> HOLE == E:Exp => V == E  [cool]

  rule V:RVal ~> E:Exp == HOLE => E == V  [cool]

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

  //@ Heating the argument of the prefix increment as an lvalue;
  context ++ (HOLE => lvalue(HOLE))

 //@ EXtend the above heating for nested increment expressions:

  rule lvalue(++ E:Exp) => ++ E:Exp ~> lvalue(HOLE) [heat]
  rule L:Loc ~> lvalue(HOLE) => lvalue(L) [cool]

  //@ The semantics of the the prefix increment
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
  (see 5.3.2 and 5.2.6)."\\
  Here is the definition for sequenced before:\\
  "\emph{Sequenced before} is an asymmetric, transitive, pair-wise relation 
  between evaluations executed by a single
   thread (1.10), which induces a partial order among those evaluations.
   Given any two evaluations A and B, if
   A is sequenced before B, then the execution of A shall precede the execution
   of B. If A is not sequenced before
   B and B is not sequenced before A, then A and B are unsequenced.
  [ Note: The execution of unsequenced
   evaluations can overlap. — end note ] Evaluations A and B are 
  indeterminately sequenced when either A
   is sequenced before B or B is sequenced before A, but it is unspecified 
  which.
  [ Note: Indeterminately
   sequenced evaluations cannot overlap, but either could be executed first.
   — end note ]\\
  Every value computation and side effect associated with a full-expression
  is sequenced before every value
  computation and side effect associated with the next full-expression
  to be evaluated."\\
  */

  /*@
   We add a new cell that collects the side-effects during the evaluation
   of a full-expression:
  */

  configuration 
     <sideEffects> .K </sideEffects>

  /*@
  we define a syntax for the side-effects;
  */

  syntax K ::= "$inc" "(" K ")" | "$dec" "(" K ")" | "seqpoint"

  
  //@ The argument of the postfix increment operator is heated as an lvalue:
  context (HOLE => lvalue(HOLE)) ++

  /*@
    The semantics of the postfix increment operator: the result value is the 
    value  stored at the computed location and its side-effect is added to 
    the cell with the side-effects:
  */

  rule <k> L:Loc ++ => V ...</k>
       <store>... L |-> V:Int ...</store>
       <sideEffects> . => $inc(L) ...</sideEffects>

  /*@
    The semantics of a sequence point (when a full-expression is sequenced):
    the sequence of the side effects is moved from the its cell to the top of
    the k cell. The side-effects are executed in the reverse order they were
    evaluated.
  */

  rule <k> seqpoint => SE ...</k>
       <sideEffects> SE => . </sideEffects>

  //@ The semantics of the side-effects (self-explained);

  rule <k> $inc(L:Loc) => . ...</k>
       <store>... L |-> (V:Int => V +Int 1) ...</store>


  rule <k> $dec(L:Loc) => . ...</k>
       <store>... L |-> (V:Int => V -Int 1) ...</store>

 
endmodule
