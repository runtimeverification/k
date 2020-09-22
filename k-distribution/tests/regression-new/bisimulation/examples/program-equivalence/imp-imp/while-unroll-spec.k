module SYNC-POINT-CANDIDATES

imports MAIN

syntax Id ::= "n" [token]

claim
<s> ~ a => ^ b ... </s>
<ak> while (_) _ </ak>
[trusted]

claim
<s> ~ a => ^ b ... </s>
<ak> .K </ak>
[trusted]

claim
<s> ~ b => ^ a ... </s>
<bk> while (_) _ </bk>
<bstate> n |-> N:Int _ </bstate>
requires N modInt 2 ==Int 0
[trusted]

claim
<s> ~ b => ^ a ... </s>
<bk> .K </bk>
[trusted]

endmodule

module WHILE-UNROLL-SPEC

imports MAIN
imports SYNC-POINT-CANDIDATES

// loop unrolling
claim
<k> check => . </k>
<s> ^ a ... </s>
<aT>
  <ak>
    while (!(10 <= n)) { // n < 10
      n = n + 2;
    }
  =>
    ?_
  </ak>
  <astate> n |-> N1:Int _ => ?_ </astate>
</aT>
<bT>
  <bk>
    while (!(10 <= n)) { // n < 10
      n = n + 1;
    }
  =>
    ?_
  </bk>
  <bstate> n |-> N2:Int _ => ?_ </bstate>
</bT>
requires N1 ==Int N2
 andBool N1 modInt 2 ==Int 0

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
