module TEST-SYNTAX
endmodule

module TEST
  imports DOMAINS

  syntax Bool ::= test(Int) [function]
  rule test(I) =>
    #let X = I #in
    X <=Int 100 andBool X >=Int 50
endmodule
