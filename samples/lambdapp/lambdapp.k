// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "../lambda/lambda.k"

module LAMBDAPP-SYNTAX
  imports LAMBDA-SYNTAX

  syntax Exp ::= "let" Id "=" Exp "in" Exp
               | "letrec" Id "=" Exp "in" Exp
               | "if" Exp "then" Exp "else" Exp
               > "mu" Id "." Exp       [binder, latex(\mu{#1}.{#2})]
  syntax Val ::= Int | Bool

  syntax Id ::= "+" | "*" | "/" | "<=" | "ite" | "callcc"

//@ Desugaring conditional into ite with thunks. Assuming that ``\$thunk'' cannot be used in programs
  syntax Id ::= "$thunk"
  rule if E:Exp then E1:Exp else E2:Exp
    => (ite E (lambda $thunk . E1) (lambda $thunk . E2)) $thunk
   [macro]

//@ Desugaring let constructs into more basic ones
  rule (letrec X:Id = E:Exp in E':Exp) => (let X = (mu X . E) in E') [macro]
  rule (let X:Id = E:Exp in E':Exp) => (lambda X . E') E [macro]

//@ I/O additions
  syntax Exp ::= "read"
  syntax Id ::= "print"
endmodule

module LAMBDAPP
  imports LAMBDAPP-SYNTAX
  imports LAMBDA

//@Recursion
  rule (mu X:Id . E:Exp) => E[(mu X . E) / X]

//@Arithmetic
  rule + I1:Int I2:Int => I1 +Int I2
  rule * I1:Int I2:Int => I1 *Int I2
  rule / I1:Int I2:Int => I1 /Int I2
  rule <= I1:Int I2:Int => I1 <=Int I2

//@Conditional
  syntax Id ::= "t" | "e"
  // this does not prevent the user from using t and e as Id in programs
  rule ite true => lambda t . lambda e . t
  rule ite false => lambda t . lambda e . e

//@Call/CC
  syntax Val ::= "cc" "(" K ")"

  rule <k> (callcc V:Val => V cc(K)) ~> K:K </k>
  rule <k> (cc(K) V:Val) ~> _ =>  V ~> K </k>


//@ Adding $\mall{white}{in}{}$ and $\mall{white}{out}{}$ cells for I/O
  configuration <k> $PGM:Exp </k>
                <in stream="stdin"> .List </in>
                <out stream="stdout"> .List </out>

  rule <k> read => I ...</k>
       <in> ListItem(I:Int) => . ...</in>


  syntax Id ::= "dummy"
  // Again, this does not prevent the user from using dummy as Id in programs
  rule [print] : <k> print I:Int => (lambda dummy . dummy) ...</k>
       <out>... (. => ListItem(I)) </out>

/*@
 Since our evaluation strategy is topmost call-by-value, we need to add
 the predicate below to specify that an id applied to a value is a value,
 thus allowing the evaluation of the second argument for arithmetic operators.
 However, we want exclude if-then-else from these ids because evaluating
 its branches might lead to non-termination in the presence of $\mu$.
 We also exclude print as it is side-effecting.
*/
  rule isVal(X:Id V:Val) => true
   when X =/=K print andBool X =/=K ite
   [anywhere]
endmodule
