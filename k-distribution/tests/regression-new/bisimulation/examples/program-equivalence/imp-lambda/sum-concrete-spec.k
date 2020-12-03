module VERIFICATION

imports MAIN

endmodule

module SYNC-POINT-CANDIDATES

imports MAIN

syntax Id ::= "n"   [token]
            | "sum" [token]
            | "f"   [token]
            | "x"   [token]

claim
<s> ~ a => ^ b ... </s>
<impk> .K </impk>
[trusted]

claim
<s> ~ b => ^ a ... </s>
<lambdak> _:Int </lambdak>
[trusted]

endmodule

module SUM-CONCRETE-SPEC

imports VERIFICATION
imports SYNC-POINT-CANDIDATES

claim
<k> check => . </k>
<s> ^ a ... </s>
<impT>
  <impk>
    int n, sum;
    n = 3;
    sum = 0;
    while (!(n <= 0)) {
      sum = sum + n;
      n = n + -1;
    }
  =>
    ?_
  </impk>
  <impstate> .Map => ?_ </impstate>
</impT>
<lambdaT>
  <lambdak>
    letrec f x = if x <= 0 then 0 else (x + (f (x + -1)))
    in (f 3)
  =>
    ?_
  </lambdak>
  <lambdaenv> .Map => ?_ </lambdaenv>
  <lambdastore> .Map => ?_ </lambdastore>
  <lambdacounter> 1 => ?_ </lambdacounter>
</lambdaT>

claim
<k> check => . </k>
<s> ^ a ... </s>
<impT>
  <impk> .K </impk>
  <impstate> sum |-> N1:Int _:Map </impstate>
</impT>
<lambdaT>
  <lambdak> N2:Int </lambdak>
  <lambdaenv> _:Map </lambdaenv>
  <lambdastore> _:Map </lambdastore>
  <lambdacounter> _ </lambdacounter>
</lambdaT>
requires N1 ==Int N2
[trusted]

endmodule
