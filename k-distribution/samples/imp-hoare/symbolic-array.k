// Copyright (c) 2013-2015 K Team. All Rights Reserved.
require "builtins/array.k"

module SYMBOLIC-ARRAY-SYNTAX
  imports ARRAY-SYNTAX
  syntax KResult ::= "select" "(" Array "," Int ")" [smtlib(select)]
endmodule

module SYMBOLIC-ARRAY
  imports ARRAY-SYNTAX
endmodule