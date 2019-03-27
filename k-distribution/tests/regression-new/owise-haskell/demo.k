module DEMO

  imports DOMAINS

  syntax S ::= "a" | f(S)
  syntax Bool ::= S "lt" S [function]
  rule a lt f(X) => true
  rule f(X) lt f(Y) => X lt Y
  rule X lt Y => false [owise]
endmodule
