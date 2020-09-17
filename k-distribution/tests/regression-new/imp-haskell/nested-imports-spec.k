/*
*/

module MODULE
    imports IMP
endmodule

module VERIFICATION
  imports MODULE

  syntax Id ::= "a" [token]
  syntax Id ::= "b" [token]
  syntax Id ::= "max" [token]
endmodule


module NESTED-IMPORTS-SPEC [one-path]
  imports IMP
  imports VERIFICATION

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
