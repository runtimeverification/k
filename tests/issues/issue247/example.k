module ISSUE-SYNTAX
	syntax Exp  ::= #Int | Exp "+" Exp [strict] | "[" Exps "]" [strict]
        syntax Exps ::= List{Exp,","} [prec 120]
end module

module ISSUE
  imports ISSUE-SYNTAX
  syntax KResult ::= #Int 
  rule I1:#Int + I2:#Int => I1 +Int I2

  syntax Bag ::= test1 | test2 
  rule test1 => <k> [3+5,7+9,2+12] </k>
  rule test2 => <k> [8,16,14] </k>
  syntax #Bool ::= "equal" "(" Bag "," Bag ")"
  rule equal(X:Bag,X:Bag) => true
end module 
