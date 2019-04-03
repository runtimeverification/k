// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "domains.k"

module FFI-SYNTAX
  imports INT-SYNTAX
  imports FLOAT-SYNTAX

  syntax FFIType ::= Int | Float | "#void" [klabel(#void), symbol]
endmodule

module FFI
  imports FFI-SYNTAX
  imports BYTES
  imports LIST

  /*@ The FFI call takes a list of bytes, a list of types, and a return type. */
  syntax Bytes ::= "#ffiCall" "(" List "," List "," FFIType ")" [function, hook(FFI.call), impure]
endmodule
