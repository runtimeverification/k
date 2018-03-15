module TEST
  imports DOMAINS

  configuration
    <k> $PGM:Pgm </k>
    <set> .Set </set>

  syntax Pgm ::= start(Int)
               | mid(Int)
               | "end"

  rule
    <k> start(I) => mid(I) ...</k>
    <set>... .Set => SetItem(I) ...</set>
endmodule
