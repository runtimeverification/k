requires "lesson-16-a.k"

module LESSON-16-C-SYNTAX
  imports LESSON-16-A-SYNTAX
endmodule

module LESSON-16-C
  imports LESSON-16-C-SYNTAX
  imports BOOL
  imports SET

  configuration <T>
                  <k> $PGM:Pgm </k>
                  <state> .Map </state>
                  <declared> .Set </declared>
                </T>

  rule  <k> D:Decl P:Pgm => D ~> P ...</k>
  rule  <k> .Pgm => . ...</k>

  rule  <k> int X:Id = I:Int ; => . ...</k>
        <state> STATE => STATE [ X <- I ] </state>
        <declared> D => D SetItem(X) </declared>

  rule  <k> X:Id => I ...</k>
        <state>... X |-> I ...</state>
        <declared>... SetItem(X) ...</declared>

  syntax Bool ::= isKResult(K) [symbol, function]
  rule isKResult(_:Int) => true
  rule isKResult(_) => false [owise]
endmodule
