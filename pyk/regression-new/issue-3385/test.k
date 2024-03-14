// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
  imports K-EQUAL
  syntax Thing ::= "a" [token]
                 | "b" [token]
                 | "c" [token]
  syntax Thing ::= f ( Thing ) [ function, total ]

  rule [f-of-a-is-b] : f(A) => b requires A ==K a // [concrete]
  rule [f-otherwise] : f(_) => c                   [owise]
endmodule
