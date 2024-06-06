// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module EXISTSLHSBOUNDPASS-SYNTAX
  imports INT-SYNTAX
endmodule

module EXISTSLHSBOUNDPASS
  imports EXISTSLHSBOUNDPASS-SYNTAX
  imports INT

  syntax Exp ::= foo(Int)
  rule foo(_X) => #Exists Y . { ?_I #Equals Y }
endmodule
