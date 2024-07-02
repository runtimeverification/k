// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKEXCLUDESIMPLIFICATION-SYNTAX
endmodule

module CHECKEXCLUDESIMPLIFICATION
  imports CHECKEXCLUDESIMPLIFICATION-SYNTAX
  imports INT

syntax Int ::= f(Int)  [function, total]
syntax Int ::= g(Int)  [function, total]

rule g(f(X)) => X [simplification]

endmodule
