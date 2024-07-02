module TEST
  imports ID

  syntax LVal ::= L()
  syntax Exp  ::= E()
                | LVal
  
  syntax Exp  ::= Exp  "." Id [overload(_._)]
  syntax LVal ::= LVal "." Id [overload(_._)]

  syntax KItem ::= done()
  rule _:LVal => done()
endmodule
