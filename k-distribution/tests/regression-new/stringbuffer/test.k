module TEST
  imports STRING-BUFFER

  rule 0 => foo(.StringBuffer, 0)

  syntax String ::= foo(StringBuffer, Int) [function]

  rule foo(S::StringBuffer, 0) => foo(S +String "hello ", 1)
  rule foo(S::StringBuffer, 1) => foo(S +String "world!", 2)
  rule foo(S::StringBuffer, 2) => StringBuffer2String(S)

endmodule
