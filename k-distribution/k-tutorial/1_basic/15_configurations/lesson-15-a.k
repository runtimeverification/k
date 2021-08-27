module LESSON-15-A-SYNTAX
  imports INT-SYNTAX

  syntax Ints   ::= List{Int, ","}
endmodule

module LESSON-15-A
  imports LESSON-15-A-SYNTAX
  imports INT

  configuration <k> $PGM:Ints </k>
                <sum> 0 </sum>

  rule  <k> I:Int, Is:Ints => Is ...</k>
        <sum> SUM:Int => SUM +Int I </sum>
endmodule
