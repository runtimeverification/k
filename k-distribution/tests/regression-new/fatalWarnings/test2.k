module TEST2-SYNTAX

endmodule

module TEST2
imports TEST2-SYNTAX

syntax Foo ::= "foo" "(" Foo ")"

rule foo ( A ) => A

endmodule
