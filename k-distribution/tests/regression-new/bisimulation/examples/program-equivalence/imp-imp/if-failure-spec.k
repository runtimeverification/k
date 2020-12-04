module SYNC-POINT-CANDIDATES

imports MAIN

claim
<s> ~ a => ^ b ... </s>
<ak> .K </ak>
[trusted]

claim
<s> ~ b => ^ a ... </s>
<bk> .K </bk>
[trusted]

endmodule

module IF-FAILURE-SPEC

imports MAIN
imports SYNC-POINT-CANDIDATES

syntax Id ::= "n" [token]

// wrong code motion
claim
<k> check => . </k>
<s> ^ a ... </s>
<aT>
  <ak>
    n = n + 1;
    if (n <= 0) {
    } else {
      n = n + 1;
    }
  =>
    ?_
  </ak>
  <astate> n |-> N1:Int _ => ?_ </astate>
</aT>
<bT>
  <bk>
    if (n <= 0) {
      n = n + 1;
    } else {
      n = n + 1;
      n = n + 1;
    }
  =>
    ?_
  </bk>
  <bstate> n |-> N2:Int _ => ?_ </bstate>
</bT>
requires N1 ==Int N2

claim
<k> check => . </k>
<s> ^ a ... </s>
<aT>
  <ak> .K </ak>
  <astate> n |-> N1:Int _ </astate>
</aT>
<bT>
  <bk> .K </bk>
  <bstate> n |-> N2:Int _ </bstate>
</bT>
requires N1 ==Int N2
[trusted]

endmodule
