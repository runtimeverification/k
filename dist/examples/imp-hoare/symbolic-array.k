module SYMBOLIC-ARRAY-SYNTAX
  syntax Array ::= "store" "(" Array "," Int "," K ")" [smtlib(store)]
  syntax KResult ::= "select" "(" Array "," Int ")" [smtlib(select)]
endmodule

module SYMBOLIC-ARRAY
  imports ARRAY-SYNTAX
endmodule