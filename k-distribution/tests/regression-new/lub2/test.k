module TEST
  imports BOOL
  imports K-EQUAL

  syntax KItem ::= foo() | bar()

  rule <k> foo() => #if true #then bar() #else .K #fi ~> bar() ...</k>

endmodule
