// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module SYMBOLIC-ARRAY-SYNTAX
  syntax KResult ::= "select" "(" Array "," Int ")" [smtlib(select)]
endmodule

module SYMBOLIC-ARRAY
  imports ARRAY-SYNTAX
endmodule