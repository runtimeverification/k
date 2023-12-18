// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
  imports INT

syntax K ::= foo() [function]

rule foo() => 0

rule 1 => {foo()}:>KItem

endmodule
