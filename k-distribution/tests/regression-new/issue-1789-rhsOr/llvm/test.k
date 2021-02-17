module TEST-SYNTAX
  imports INT-SYNTAX
  syntax Exp ::= "a" | "b" | "bar" | "baz"
  syntax Exp ::= Int
endmodule

module TEST
  imports TEST-SYNTAX
  imports INT

  configuration <k> $PGM:Exp </k>
                <foo> .K </foo>

  rule <k> 1 => a </k>
       <foo> _ => bar </foo>

  rule <k> 2 => a </k>
       <foo> _ => baz </foo>

  rule <k> a => b ... </k>
       <foo> bar #Or baz </foo>

endmodule
