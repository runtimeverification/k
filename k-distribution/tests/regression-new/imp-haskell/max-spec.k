// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
/*
*/

module VERIFICATION
  imports IMP

  syntax Id ::= "a" [token]
  syntax Id ::= "b" [token]
  syntax Id ::= "max" [token]
endmodule


module MAX-SPEC [one-path]
  imports VERIFICATION
  imports IMP

  claim
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
    ensures (A >=Int B andBool ?M ==Int A) orBool (B >=Int A andBool ?M ==Int B)

endmodule
