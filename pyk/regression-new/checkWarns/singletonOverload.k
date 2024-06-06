module SINGLETONOVERLOAD-SYNTAX
endmodule

module SINGLETONOVERLOAD
  imports ID

  syntax LVal ::= L() [unused]
                | LVal "." Id [unused, overload(_.)]
  syntax Exp  ::= LVal
                | Exp  "." Id [unused, overload(_._)]
endmodule
