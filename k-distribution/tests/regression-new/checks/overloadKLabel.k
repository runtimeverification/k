// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module OVERLOADKLABEL
  imports ID
  syntax Exp  ::= LVal
                | Exp  "." Id [klabel(_._), overload(_._)]
  syntax LVal ::= LVal "." Id [overload(_._)]
endmodule
