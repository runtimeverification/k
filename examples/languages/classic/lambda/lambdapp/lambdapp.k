require ../untyped/lambda

module LAMBDAPP-SYNTAX
  imports LAMBDA-SYNTAX
  
  syntax Exp ::= "mu" #Id "." Exp       [:binder prec 100 latex "\mu{#1}.{#2}":] 
               | "let" #Id "=" Exp "in" Exp  
               | "letrec" #Id "=" Exp "in" Exp  
  syntax Val ::= #Int | #Bool

  syntax #Id ::= "+" | "*" | "/" | "<=" | "ite" | "callcc"

//@ Desugaring let constructs into more basic ones
  macro (letrec X = E in E') = (let X = (mu X.E) in E')
  macro (let X:#Id = E:Exp in E':Exp) = (lambda X.E') E

//@ I/O additions
  syntax Exp ::= "read"
  syntax #Id ::= "print"

end module

module LAMBDAPP
  imports LAMBDAPP-SYNTAX + LAMBDA

//@Recursion
  rule <k> (mu X:#Id.E:Exp) => E[(mu X.E) / X] ...</k>

//@Arithmetic
  rule + I1:#Int I2:#Int => I1 +Int I2
  rule * I1:#Int I2:#Int => I1 *Int I2
  rule / I1:#Int I2:#Int => I1 /Int I2
  rule <= I1:#Int I2:#Int => I1 <=Int I2

//@Conditional
  rule ite true E _ => E
  rule ite false _ E => E

//@Call/CC
  syntax Val ::= "cc" "(" K ")"

  rule <k> (callcc V => V cc(K)) ~> K:K </k>
  rule <k> (cc(K) V) ~> _ =>  V ~> K </k>
  

//@ Adding $\mall{white}{in}{}$ and $\mall{white}{out}{}$ cells for I/O
  configuration <k> $PGM:Exp </k>
                <in stream="stdin"> .List </in>
                <out stream="stdout"> .List </out>

  rule <k> read => I ...</k> 
       <in> ListItem(I:#Int) => . ...</in>


  syntax #Id ::= "dummy"
  rule [print] : <k> print I => (lambda dummy.dummy) ...</k>
       <out>... (. => ListItem(I)) </out>

/*@ 
 Since our evaluation strategy is topmost call-by-value, we need to add 
 the predicate below to specify that an id applied to a value is a value,
 thus allowing the evaluation of the second argument for arithmetic operators.
 However, we want exclude if-then-else from these ids because evaluating
 its branches might lead to non-termination in the presence of $\mu$.
 We also exclude print as it is side-effecting.
*/
  rule 'k-result(X:#Id V:Val) => true 
   if X =/=Bool print andBool X =/=Bool ite

end module
