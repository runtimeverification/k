require "ffi.md"
require "json.md"
require "rat.md"
require "substitution.k"

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
