module ISSUE
  syntax KItem ::= "foo"

  configuration <k> foo </k>

  rule _:KItem => .
endmodule

