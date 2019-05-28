/*
*/

module VERIFICATION
  imports IMP

  syntax Id ::= "a" [token]
  syntax Id ::= "b" [token]
  syntax Id ::= "max" [token]
endmodule


module MAX-BROKEN-SPEC
  imports VERIFICATION
  imports IMP

  rule
    <k>
if (a <= b)
{ max = b; }
else
{ max = a; }
=> .K
    </k>
    <state>
    a |-> A:Int
    b |-> B:Int
    max |-> (_ => ?M:Int)
    </state>
    ensures (A >=Int B andBool ?M ==Int A)

endmodule
