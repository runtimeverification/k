// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "ffi.md"
requires "json.md"
requires "rat.md"
requires "substitution.md"

module TEST-SYNTAX
endmodule

module TEST
  imports DOMAINS
  imports ARRAY
  imports COLLECTIONS
  imports FLOAT
  imports STRING-BUFFER
  imports BYTES
  imports K-IO
  imports DEFAULT-STRATEGY
  imports MINT
  imports FFI
  imports JSON
  imports RAT
  imports SUBSTITUTION
  imports TEST-SYNTAX

  syntax MInt{8}
  rule I:Int => Int2MInt(I)::MInt{8}

  configuration <k> $PGM:K </k> <s/>
endmodule
