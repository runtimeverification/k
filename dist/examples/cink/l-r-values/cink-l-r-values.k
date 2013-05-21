require "../basic/cink-basic.k"

module CINK-L-R-VALUES-SYNTAX

  imports CINK-BASIC-SYNTAX


endmodule

module CINK-L-R-VALUES-SEMANTICS

  imports CINK-L-R-VALUES-SYNTAX

  /*@
  We first deal only with lvalues and prvalues. In order to keep the definition
  as simple as possible, we let the the prvalue as the default category for 
  expressions and we make explicitly only the category of lvalue expressions:
  */
  
  syntax K ::= "lvalue" "(" K ")"

  /*@
  As its definition says, the main operator emphasiszing the two categories is
  the assignment. We use a context declaration to say that the left-hand side 
  of the assignemnt is a lvalue:
  */

  context (HOLE => lvalue(HOLE)) = _:Exp

  /*@
  The above declaration is equivalent with the following to heating/cooling
  rules:
  \begin{align}
  & E_1 \texttt{~=~} E_2 \Rightarrow lvalue(E_1) \kra \HOLE \texttt{~=~} E_2\\
  &  lvalue(L_1) \kra \HOLE \texttt{~=~} E_2 \Rightarrow L_1 \texttt{~=~} E_2
  \end{align}
  This assume that the locations must be defined as values:
  */

  syntax Val ::= Loc 

  /*@
  An identifier seen as a lvalue is evaluated to its location: 
  */
  rule <k> lvalue(X:Id => L) ...</k>
       <env>... X |-> L:Loc ...</env>
       [lookup]

  /*@
  An assignemnt, after the reduction of the arguments, has in the lef-hand
  side a location ($=$ the lvalue designated by the lhs.)
  */
  rule <k> L:Loc = V:Val  => V ...</k>
       <store>... L |-> (_ => V) ...</store>
       [update]

  /*@
  The right-hand side of reading operator is evaluated as a lvalue:
  */
  context cin >> (HOLE => lvalue(HOLE))

  /*@
  The semantics of the reading operator is overriden:
  */
  rule <k> cin >> L:Loc => cin  ...</k>
       <store>... L |-> (_ => V)  ...</store>
       <in> (ListItem(V:Val) => .)  ...</in>
       [read-stream]

endmodule
