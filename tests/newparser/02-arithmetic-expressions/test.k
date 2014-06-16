// Copyright (c) 2014 K Team. All Rights Reserved.
module TEST

  configuration
    <k> $PGM:Exp </k>
    <env> 
	       a |-> 1
		   b |-> 2
		   c |-> 3
    </env>

  syntax Id ::= "a" | "b" | "c"
  syntax KResult ::= Int
  syntax Lit ::= Int | Id
  syntax Term ::= "(" Exp ")"  [bracket]
                | Term "*" Lit [strict]
                | Lit
  syntax Exp  ::= Exp "+" Term [strict]
                | Term
	
  rule A:Int + B:Int => A +Int B
  rule A:Int * B:Int => A *Int B
  rule <k> X:Id => V ...</k>
       <env>... X |-> V ...</env>
endmodule
