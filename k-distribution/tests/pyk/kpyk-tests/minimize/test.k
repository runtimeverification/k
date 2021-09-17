module TEST
  imports INT
  imports MAP

  configuration <k> $PGM:Step </k>
                <mem> .Map </mem>

  syntax Step ::= runLemma ( Int ) | doneLemma ( Int )
  rule <k> runLemma(I) => doneLemma(I) ... </k>

endmodule

module TEST-SPEC
  imports TEST

  claim <k> runLemma(3 +Int 4) => doneLemma(10) ... </k> <mem> _ </mem>
endmodule
