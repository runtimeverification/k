require "builtins/model-checker.k"
require "../threads/cink-threads.k"

module CINK-LTLMC-SYNTAX

  imports CINK-BASIC-SYNTAX
  imports LTL-HOOKS
  imports MODEL-CHECKER-HOOKS

  /*@
    A input program is a sequence of statements or a LTL Formula 
    (this is needed for parsing purposes)
  */
  syntax Pgm ::= LtlFormula


  /*@
    This module combines the syntax of the \Cink language with that of 
    the LTL formulas.
    The module \texttt{MODEL-CHECKER-HOOKS} is a \K interface to the Maude module 
    defining the syntax for the model-checker. 
    In addition to this interface, we have to define the atomic propositions.
    Here is an example of such proposition,
    whose intended semantics is to test whether the value of a variable in the
    configuration is equal to a given value. The semantics for this proposition
    will be given later, in the main module.  
  */

  syntax Prop ::= "eqTo" "(" Id "," Val ")"
               |  "lt" "(" Id "," Val ")" 
               |  "leq" "(" Id "," Val ")" 
               |  "gt" "(" Id "," Val ")" 
               |  "geq" "(" Id "," Val ")" 
               |  "neqTo" "(" Id "," Val ")" 

endmodule

module CINK-LTLMC-SEMANTICS

  imports CINK-LTLMC-SYNTAX

  configuration
      <T>
        <genv> .Map </genv>
        <store> .Map </store>
      </T>

  /*@
    This is the main module that combines the semantics of \Cink with the
    interface to the model-checker, given by the module \texttt{LTL-HOOKS}.
  */

  /*@ The states of the transition system to be model-checked are given
      by the configurations of \Cink programs, which are of sort \texttt{Bag}:
   */

  /*@
    In order to give semantics to the proposition \texttt{eqTo}, we use an 
    auxiliary function \texttt{val} that returns the value of a given variable
    name in a given configuration: 
   */

  syntax Int ::= "val" "(" Bag "," Id ")" [function]

  rule val(<generatedTop>... <T>...
                 <genv>... X:Id |-> L:Loc ...</genv> 
                 <store>... L |-> I:Int ...</store> 
           ...</T> ...</generatedTop>, X)
       =>
       I

  /*@
    We are ready now to give the semantics for \texttt{eqTo}$(X,I)$: it is 
    satisfied by a configuration (state) $B$ iff the value of $X$ in $B$ is
    equal to $I$: 
   */

  

  rule B:Bag |=Ltl eqTo(X:Id, I:Int) => true when val(B, X) ==K I [anywhere]

  rule B:Bag |=Ltl neqTo(X:Id, I:Int) => true when val(B, X) =/=K I [anywhere]

  rule B:Bag |=Ltl lt(X:Id, I:Int) => true when val(B, X) <Int I [anywhere]

  rule B:Bag |=Ltl leq(X:Id, I:Int) => true when val(B, X) <=Int I [anywhere]

  rule B:Bag |=Ltl gt(X:Id, I:Int) => true when val(B, X) >Int I [anywhere]

  rule B:Bag |=Ltl geq(X:Id, I:Int) => true when val(B, X) >=Int I [anywhere]

endmodule

