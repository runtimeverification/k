module INVALIDSORTPREDICATE
  imports INT
  imports BOOL

  syntax Exp

  rule isExp(I) => isInt(I) andBool configFunction()

  configuration <k> $PGM:K </k> <state> .K </state>

  syntax Bool ::= configFunction() [function]
  rule [[ configFunction() => true ]]
       <state> .K </state>

endmodule
