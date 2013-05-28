module SYMBOLIC-ARRAY-SYNTAX
  syntax KResult ::= "select" "(" Array "," Int ")" [smtlib(select)]
endmodule

module SYMBOLIC-ARRAY
  imports ARRAY-SYNTAX
endmodule