module INTOPERATIONINLHS
  imports INT
  imports MAP

syntax Int ::= "foo" "(" Int ")" [function]

rule foo(A +Int 1) => 0

syntax Int ::= bar(Map) [function]

rule bar(foo(0) |-> 0) => 0

rule [[ bar(0 |-> 0) => foo(0) ]]
     <k> .K </k>

rule [[ bar(0 |-> 0) => 0 ]]
     <k> foo(0) </k>

rule [[ bar(0 |-> foo(0)) => foo(0) ]]
     <k> .K </k>

endmodule
