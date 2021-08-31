module DEMO
  imports BOOL

  syntax S ::= "a" | f(S)
  syntax Bool ::= S "lt" S [function]
  rule a lt f(_X) => true
  rule f(X) lt f(Y) => X lt Y
  rule _X lt _Y => false [owise]
endmodule
