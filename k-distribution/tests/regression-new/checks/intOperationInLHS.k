module INTOPERATIONINLHS
  imports INT

syntax KItem ::= "foo" "(" Int ")"

rule foo(A +Int 1) => .K

endmodule
