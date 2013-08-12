module ISSUE
  syntax Foo ::= foo(Int, Int)
  rule foo(A, B) => A +Int B
endmodule

