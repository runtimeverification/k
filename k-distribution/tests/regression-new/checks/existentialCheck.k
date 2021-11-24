module EXISTENTIALCHECK

  imports K-EQUAL
  imports BOOL

  syntax Program ::= "stateA" | "stateB"
  syntax Bool ::= isDone(Program) [function]

  rule stateA => stateB

  rule isDone(stateB) => true
  rule isDone(_) => false [owise]

  claim <k> ?X:Int => . </k>

  rule <k> ?X:Int => . </k>

  rule <k> stateA => ?STATE </k>
    requires isDone(?STATE)

endmodule
