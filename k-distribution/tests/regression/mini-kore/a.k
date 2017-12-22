module A-SYNTAX
syntax Exp ::= Int
             | Exp "+" Exp
endmodule

module A
imports A-SYNTAX
configuration <T>
  <k> $PGM:Exp </k>
</T>
endmodule
