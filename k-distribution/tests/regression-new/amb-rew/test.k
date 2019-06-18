module TEST-SYNTAX
endmodule

module TEST
  imports TEST-SYNTAX
  imports INT
  imports MAP
  imports ID

syntax Type ::= "type"
syntax Foo ::= foo(Map)

rule foo(1 |-> 0 => 1 |-> #fun(T::Type => T |-> T)(type))


endmodule
