module TEST
  imports INT
  imports LIST

syntax List ::= foo(List, List) [function]

rule foo(.List, (.List ListItem(I::Int))) => .List

endmodule
