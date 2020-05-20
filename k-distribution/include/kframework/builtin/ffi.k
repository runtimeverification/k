// Copyright (c) 2019 K Team. All Rights Reserved.
require "domains.k"

module FFI-SYNTAX
  imports LIST
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
                  | "#struct" "(" List ")" [klabel(#struct), symbol]
endmodule

module FFI
  imports FFI-SYNTAX
  imports BYTES
  imports STRING

  /*@ The FFI call takes an int for the symbol to call, a list of bytes, a list of types, and a return type. */
  syntax Bytes ::= "#ffiCall" "(" Int "," List "," List "," FFIType ")" [function, hook(FFI.call)]
  /*@ The variadic FFI call takes an int for the symbol to call, a list of bytes, a list of fixed types, a list of variadic types and a return type. */
                 | "#ffiCall" "(" Int "," List "," List "," List "," FFIType ")" [function, hook(FFI.call_variadic)]
  /*@ The FFI call takes a boolean isVariadic, an int for the symbol to call, a list of bytes, a list of types and a return type. */
                 | "#ffiCall" "(" Bool "," Int "," List "," List "," Int "," FFIType ")" [function]

  /*@ Given a function symbol, return its address as an Int */
  syntax Int ::= "#functionAddress" "(" String ")" [function, hook(FFI.address)]

  rule #ffiCall(false, Addr::Int, Args::List, Types::List, _, Ret::FFIType) => #ffiCall(Addr, Args, Types, Ret)
  rule #ffiCall(true, Addr::Int, Args::List, Types::List, NFixed::Int, Ret::FFIType) => #ffiCall(Addr, Args, range(Types, 0, size(Types) -Int NFixed), range(Types, NFixed, 0), Ret)
endmodule
