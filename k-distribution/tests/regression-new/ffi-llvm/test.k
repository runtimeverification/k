requires "ffi.k"

module TEST-SYNTAX
  imports FFI-SYNTAX
endmodule

module TEST
  imports TEST-SYNTAX
  imports FFI
endmodule
