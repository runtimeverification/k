// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module TEST
  syntax #Bool ::= "true"
  syntax #Bool ::= "false"
  syntax Bool ::= #Bool

  syntax Bool ::= "notBool" Bool

  rule notBool true => false
  rule notBool false => true

  rule 'notBool(true) => false

  syntax Bools ::= List{Bool, ","}

  rule true, true => .Bools
endmodule
