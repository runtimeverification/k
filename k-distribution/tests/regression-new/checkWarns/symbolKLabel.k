module SYMBOLKLABEL-SYNTAX
endmodule

module PW1
  syntax Foo ::= "foo" [klabel(foo), symbol, unused]
endmodule

module PW2
    syntax Foo ::= "foo" [klabel(foo), unused]
endmodule

module PW3
    syntax Foo ::= Bar
    syntax Foo ::= "foo" Foo [klabel(foo), unused]
    syntax Bar ::= "foo" Bar [klabel(foo), unused]
endmodule

module SYMBOLKLABEL
  imports PW1
  imports PW2
  imports PW3
endmodule
