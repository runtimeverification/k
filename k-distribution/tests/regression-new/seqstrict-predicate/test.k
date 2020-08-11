module TEST
  imports INT

  context alias [foo]: HERE [result(Foo)]

  syntax Exp ::= Exp "+" Exp [seqstrict(foo), left] | Int

  syntax Foo ::= Int

  rule I + J => I +Int J

endmodule
