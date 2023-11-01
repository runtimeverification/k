// Copyright (c) K Team. All Rights Reserved.
requires "ffi.md"

module TEST-SYNTAX
  imports FFI-SYNTAX
endmodule

module TEST
  imports TEST-SYNTAX
  imports FFI
endmodule
