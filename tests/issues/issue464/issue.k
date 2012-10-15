module ISSUE
  syntax A ::= "a"
  syntax B ::= List{A,""}
  rule a a => a
endmodule

