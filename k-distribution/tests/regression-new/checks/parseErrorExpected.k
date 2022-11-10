module PARSEERROREXPECTED
  imports INT

syntax Foo ::= "foo" "bar"

rule => false
rule 0 => true
rule <k> 0 => true </k>
rule
rule foo


endmodule
