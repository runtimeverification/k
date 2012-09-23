require "bool.k"
module INT-SYNTAX-HOOKS
  imports #INT-INTERFACE
  syntax Int ::= #Int
endmodule

module INT-HOOKS
  imports INT-SYNTAX-HOOKS 
  imports BOOL-HOOKS

  syntax Int ::= right:
  				 "~Int" Int [function, right, latex(\mathop{\sim_{\scriptstyle\it Int}}{#1}), hook(#INT:~Int_)]
  			   > left:
  				 Int "^Int" Int [function, left, latex({#1}\mathrel{{\char`\^}_{\!\scriptstyle\it Int}}{#2}), hook(#INT:_^Int_)]
  			   > left:
  				 Int "*Int" Int [function, left, latex({#1}\mathrel{\ast_{\scriptstyle\it Int}}{#2}), hook(#INT:_*Int_)]
			   | Int "/Int" Int [function, left, latex({#1}\mathrel{\div_{\scriptstyle\it Int}}{#2}), hook(#INT:_/Int_)]
			   | Int "%Int" Int [function, left, latex({#1}\mathrel{\%_{\scriptstyle\it Int}}{#2}), hook(#INT:_%Int_)]
			   > left:
			   	 Int "+Int" Int [function, left, latex({#1}\mathrel{+_{\scriptstyle\it Int}}{#2}), hook(#INT:_+Int_), cons(Int1PlusSyn)]
			   | Int "-Int" Int [function, left, latex({#1}\mathrel{-_{\scriptstyle\it Int}}{#2}), hook(#INT:_-Int_)]
			   > left:
				 Int ">>Int" Int [function, left, latex({#1}\mathrel{\gg_{\scriptstyle\it Int}}{#2}), hook(#INT:_>>Int_)]
			   | Int "<<Int" Int [function, left, latex({#1}\mathrel{\ll_{\scriptstyle\it Int}}{#2}), hook(#INT:_<<Int_)]
			   > left:
				 Int "&Int" Int [function, left, latex({#1}\mathrel{\&_{\scriptstyle\it Int}}{#2}), hook(#INT:_&Int_)]
			   > left:
				 Int "xorInt" Int [function, left, latex({#1}\mathrel{\oplus_{\scriptstyle\it Int}}{#2}), hook(#INT:_xorInt_)]
			   > left:
				 Int "|Int" Int [function, left, latex({#1}\mathrel{|_{\scriptstyle\it Int}}{#2}), hook(#INT:_|Int_)]

  syntax Bool ::= Int "<=Int" Int	[function, left, latex({#1}\mathrel{\leq_{\scriptstyle\it Int}}{#2}), hook(#INT:_<=Int_)]
				| Int "<Int" Int	[function, left, latex({#1}\mathrel{<_{\scriptstyle\it Int}}{#2}), hook(#INT:_<Int_)]
				| Int ">=Int" Int	[function, left, latex({#1}\mathrel{\geq_{\scriptstyle\it Int}}{#2}), hook(#INT:_>=Int_)]
				| Int ">Int" Int	[function, left, latex({#1}\mathrel{>_{\scriptstyle\it Int}}{#2}), hook(#INT:_>Int_)]
				| Int "==Int" Int	[function, left,latex({#1}\mathrel{{=}{=}_{\scriptstyle\it Int}}{#2}), hook(#INT:_==Int_)]
				| Int "=/=Int" Int	[function, left,latex({#1}\mathrel{{=}{/}{=}_{\scriptstyle\it Int}}{#2})]

  rule I1:Int =/=Int I2:Int => notBool(I1 ==Int I2) [function, anywhere]

  //sort Nat  // ::= {I:Int | I >=Int 0}
  syntax Nat ::= "dummyNat"
  rule isNat(I:Int) => I >=Int 0 [function, anywhere]

  syntax Bool ::= Int "dividesInt" Int    [function]
  rule I1:Int dividesInt I2:Int => I2 %Int I1 ==Int 0 [function, anywhere]

  syntax Int ::= "absInt" "(" Int ")" [function, klabel(absInt)]
  rule absInt(I:Int) => I when isNat(I) [function, anywhere]
  rule absInt(I:Int) => 0 -Int I when notBool(isNat(I)) [function, anywhere]

endmodule
