module SINGLETONOVERLOAD-SYNTAX
endmodule

module WARNS
  imports ID

  syntax LVal ::= L() [unused]
                | LVal "." Id [unused, overload(_.)]
  syntax Exp  ::= LVal
                | Exp  "." Id [unused, overload(_._)]
endmodule

module NOWARNS
  imports DOMAINS

  syntax Foo  ::= "foo" | "bar"
  syntax Foos ::= List{Foo, ","}
  
  syntax Bool ::= test(Foo)   [function, overload(test)]
                | test(Foos)  [function, overload(test)]

  rule test(foo) => true
  rule test(bar) => false

  rule test(F, Rest) => test(F) andBool test(Rest)
  rule test(.Foos) => true

  syntax KItem ::= disambiguate(KItem, KItem) [overload(disambiguate), unused]
                 | disambiguate(List, Set)    [overload(disambiguate), unused]
endmodule

module SINGLETONOVERLOAD
  imports WARNS
  imports NOWARNS
endmodule
