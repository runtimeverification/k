module LESSON-15-B-SYNTAX
  imports INT-SYNTAX
endmodule

module LESSON-15-B
  imports LESSON-15-B-SYNTAX
  imports INT
  imports BOOL

  configuration <k> . </k>
                <first> $FIRST:Int </first>
                <second> $SECOND:Int </second>

  rule  <k> . => FIRST >Int SECOND </k>
        <first> FIRST </first>
        <second> SECOND </second>
endmodule
