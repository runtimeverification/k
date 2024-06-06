module TEST
  imports DOMAINS

  syntax Foo ::= "foo"
  syntax Bar ::= Foo | "bar"

  syntax Bool ::= test(Foo) [function, overload(test)]
                | test(Bar) [function, overload(test)]

  rule test(foo) => true
  rule test(_)   => false
endmodule
