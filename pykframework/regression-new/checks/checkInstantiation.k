// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKINSTANTIATION-SYNTAX
  imports MINT-SYNTAX
endmodule

module CHECKINSTANTIATION
  imports CHECKINSTANTIATION-SYNTAX
  imports MINT

  syntax KItem ::= foo(MInt{6})

endmodule
