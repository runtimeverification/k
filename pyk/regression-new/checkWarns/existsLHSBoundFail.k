// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module EXISTSLHSBOUNDFAIL-SYNTAX
  imports INT-SYNTAX
endmodule

module EXISTSLHSBOUNDFAIL
  imports EXISTSLHSBOUNDFAIL-SYNTAX
  imports INT

  syntax Exp ::= foo(Int)
  rule foo(X) => #Exists Y . { I #Equals Y }
endmodule
