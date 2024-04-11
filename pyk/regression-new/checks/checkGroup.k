// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKGROUP
  syntax Int ::= r"[\\+-]?[0-9]+" [prefer, token, prec(2)]
               | Int "+" Int [group(fun,)]
endmodule
