// Copyright (c) 2019 K Team. All Rights Reserved.
require "domains.k"

module FFI-SYNTAX
  imports INT-SYNTAX
  imports FLOAT-SYNTAX

  syntax FFIType ::= "#void" [klabel(#void), symbol]
                  | "#uint8" [klabel(#uint8), symbol]
                  | "#sint8" [klabel(#sint8), symbol]
                  | "#uint16" [klabel(#uint16), symbol]
                  | "#sint16" [klabel(#sint16), symbol]
                  | "#uint32" [klabel(#uint32), symbol]
                  | "#sint32" [klabel(#sint32), symbol]
                  | "#uint64" [klabel(#uint64), symbol]
                  | "#sint64" [klabel(#sint64), symbol]
                  | "#float" [klabel(#float), symbol]
                  | "#double" [klabel(#double), symbol]
                  | "#uchar" [klabel(#uchar), symbol]
                  | "#schar" [klabel(#schar), symbol]
                  | "#ushort" [klabel(#ushort), symbol]
                  | "#sshort" [klabel(#sshort), symbol]
                  | "#uint" [klabel(#uint), symbol]
                  | "#sint" [klabel(#sint), symbol]
                  | "#ulong" [klabel(#ulong), symbol]
                  | "#slong" [klabel(#slong), symbol]
                  | "#longdouble" [klabel(#longdouble), symbol]
                  
endmodule

module FFI
  imports FFI-SYNTAX
  imports BYTES
  imports LIST
  imports STRING

  /*@ The FFI call takes a string for the symbol to call, a list of bytes, a list of types, and a return type. */
  syntax Bytes ::= "#ffiCall" "(" String "," List "," List "," FFIType ")" [function, hook(FFI.call), impure]
endmodule
