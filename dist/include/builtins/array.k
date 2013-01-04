module ARRAY-SYNTAX
  syntax Array ::= "store" "(" Array "," Int "," K ")" [smtlib(store)]
  syntax KResult ::= "select" "(" Array "," Int ")" [smtlib(select)]
endmodule

module ARRAY
  imports ARRAY-SYNTAX
endmodule