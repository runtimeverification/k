module ISSUE

  // testing lexical tokens allowing "|" in the regular expression
  // this means strings can be defined directly in K

  syntax MyString ::= Token{"'" ((~[\'\n\r\\])|([\\]~[\n\r]))* "'"}
  configuration <k> $PGM:MyString </k>
  rule 'abc' => .K

endmodule
