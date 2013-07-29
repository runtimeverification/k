require "../pointers/cink-pointers.k"

/*@ \section{The New Module}

*/

module CINK-CALL-BY-REF-SEMANTICS

  imports CINK-POINTERS-SYNTAX
  imports CINK-POINTERS-SEMANTICS

/*@
From the \Cpp manual:
\begin{quote}
a function can change the values of its non-const parameters, 
but these changes cannot affect the
values of the arguments except where a parameter is of a reference 
type (8.3.2)\ldots
\end{quote}
*/

  context evaluate((HOLE => lvalue(HOLE)), _:Exps) to _:Vals
          following  (T:Type (& X:Id)::Exp, _:Decls);


  /*@ For call-by-reference, the location pointed to by the lvalue is directly
      bound to the formal parameter. This is achieved by exactly one rule:
  */

  rule <k> bind((L:LVal, Vs:Vals) => Vs)
           to((T:Type & X:Id, Xl:Decls) => Xl); 
       ...</k>
       <env> Env:Map => Env[L/X] </env> 
  

endmodule
