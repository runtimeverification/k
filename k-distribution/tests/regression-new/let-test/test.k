module TEST
  imports INT

  syntax Exp ::= foo(Exp) | Int

  rule 0 => #let FOO = 1 #in FOO
  rule 2 => #let FOO = 3 #in #let BAR = FOO #in BAR
  rule E:Exp => #let foo(F) = E #in #let BAR = F #in #let BAZ = BAR +Int 1 #in foo(BAZ)
    requires E =/=K foo(1) andBool notBool isInt(E) [owise]

endmodule
