// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
  imports INT
  imports LIST

syntax List ::= foo(List, List) [function]

rule foo(.List, (.List ListItem(_I::Int))) => .List

endmodule
