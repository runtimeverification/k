// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module BADFUNCTIONRULEWITHCONTEXT
  imports INT
  imports BOOL
  imports MAP

syntax Int ::= foo(Int) [function]

configuration <k> $PGM:K </k> <bar> 0 </bar>

rule [[ foo(I:Int) => false ]]
     <bar> I </bar>

rule true => foo(0)

endmodule
