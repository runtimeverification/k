// Copyright (c) 2014 K Team. All Rights Reserved.
module ISSUE
  // When parsed in rules, the token "Main" should become a #token of sort Id
  // because it was declared as a single token under Id which is a Lexer sort.\
  // Before it was klabel.
  syntax Id ::= "Main"
  configuration <k> String2Id("Main") </k>
  rule K => . when K ==K Main
endmodule
