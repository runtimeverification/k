// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKSORTDECLISSUE3038-SYNTAX
  imports STRING

  syntax Token ::= "token" [token]

  syntax Token ::= String2Token( String ) [function, total, hook(STRING.string2token)]

  syntax Nested ::= nested( Token )

endmodule

module CHECKSORTDECLISSUE3038
  imports CHECKSORTDECLISSUE3038-SYNTAX

  //syntax Token
  syntax Nested ::= "NESTED_ALIAS" [alias]
  rule NESTED_ALIAS => nested( String2Token("token") )
endmodule
