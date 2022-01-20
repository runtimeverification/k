module TEST-SYNTAX
  imports INT-SYNTAX

  syntax Int ::= f(Int) [function]
  syntax KItem ::= g(Int, Int)
endmodule

module TEST
  imports TEST-SYNTAX
  imports INT

  rule f(X) => 100 +Int X [non-executable]
  rule f(X) => X requires X >=Int 100 [priority(198)]
  rule f(_) => 0 [owise]

  rule g(X, Y) => X +Int Y [non-executable, priority(1)]
  rule g(X, Y) => X requires X >=Int Y
  rule g(_, _) => 4567 [owise]
endmodule
