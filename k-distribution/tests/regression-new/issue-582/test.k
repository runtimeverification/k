module TEST
  imports INT

  syntax KResult ::= Int
  syntax Exp ::= Int | Exp "+" Exp [strict]
  rule I1:Int  + I2:Int => I1 +Int I2
endmodule
