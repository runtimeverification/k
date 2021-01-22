module TEST
  imports INT
  imports LIST

syntax List ::= foo(List, List) [function]

rule foo(.List, (.List ListItem(_I::Int))) => .List

endmodule
