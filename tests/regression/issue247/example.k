module ISSUE-SYNTAX
	syntax Exp  ::= #Int | Exp "+" Exp [strict] | "[" Exps "]" [strict]
        syntax Exps ::= List{Exp,","} [prec(120)]
end module

module ISSUE
  imports ISSUE-SYNTAX
  syntax KResult ::= #Int 
  define I1:#Int + I2:#Int => I1 +Int I2

  syntax Bool ::= test | "True" | "False"
  op check : Bag Bag -> Bool [strat(1 0) frozen(2)]
  define test => check(<k> [3+5,7+9,2+12] </k>,<k> [8,16,14] </k>)
  eq check(X:Bag,X:Bag) = True
  eq check(X:Bag,Y:Bag) = False [owise]
end module 
