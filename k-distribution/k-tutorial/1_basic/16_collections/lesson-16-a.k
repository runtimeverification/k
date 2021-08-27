module LESSON-16-A-SYNTAX
  imports INT-SYNTAX
  imports ID-SYNTAX

  syntax Exp    ::= Id | Int
  syntax Decl   ::= "int" Id "=" Exp ";" [strict(2)]

  syntax Stmt   ::= Decl
                  | Id "=" Exp ";" [strict(2)]

  syntax Pgm    ::= List{Stmt, ""}
endmodule

module LESSON-16-A
  imports LESSON-16-A-SYNTAX
  imports BOOL

  configuration <T>
                  <k> $PGM:Pgm </k>
                  <state> .Map </state>
                </T>

  rule  <k> S:Stmt P:Pgm => S ~> P ...</k>
  rule  <k> .Pgm => . ...</k>

  rule  <k> int X:Id = I:Int ; => . ...</k>
        <state> STATE => STATE [ X <- I ] </state>
        requires notBool X in_keys(STATE)

  rule  <k> X:Id = I:Int ; => . ...</k>
        <state> STATE => STATE [ X <- I ] </state>
        requires X in_keys(STATE)

  rule  <k> X:Id => I ...</k>
        <state>... X |-> I ...</state>

  syntax Bool   ::= isKResult(K) [symbol, function]
  rule isKResult(_:Int) => true
  rule isKResult(_) => false [owise]
endmodule
