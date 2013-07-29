module ISSUE
  syntax Target ::= "foo"

  rule T::Target => 0 when T =/=K 0
endmodule
