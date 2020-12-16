module VERIFICATION

imports MAIN

syntax Bool ::= sim(Int, K) [function, smtlib(sim)]

rule sim(S +Int N1, #addl1(N2) ~> _:Map ~> Ks:K) => true
requires N1 ==Int N2
 andBool sim(S, Ks) [simplification]
rule sim(0, .Map) => true

syntax Bool ::= isContinuation(K) [function, smtlib(isContinuation)]

rule isContinuation(.Map) => true
rule isContinuation(#addl1(_) ~> _:Map ~> _:K) => true

endmodule

module SYNC-POINT-CANDIDATES
imports VERIFICATION

imports MAIN

syntax Id ::= "n"   [token]
            | "sum" [token]
            | "f"   [token]
            | "x"   [token]

claim
<s> ~ a => ^ b ... </s>
<impk> while (_) _ </impk>
[trusted]

claim
<s> ~ a => ^ b ... </s>
<impk> .K </impk>
[trusted]

claim
<s> ~ b => ^ a ... </s>
<lambdak> f _:Exp ~> _Ks:K </lambdak>
[trusted]

claim
<s> ~ b => ^ a ... </s>
<lambdak> 0 ~> Ks:K </lambdak>
requires isContinuation(Ks)
[trusted]

endmodule

module SUM-SYMBOLIC-SPEC

imports VERIFICATION
imports SYNC-POINT-CANDIDATES

claim
<k> check => . </k>
<s> ^ a ... </s>
<impT>
  <impk>
    int n, sum;
    n = N1:Int;
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
    in (f N2:Int)
  =>
    ?_
  </lambdak>
  <lambdaenv> .Map => ?_ </lambdaenv>
  <lambdastore> .Map => ?_ </lambdastore>
  <lambdacounter> 1 => ?_ </lambdacounter>
</lambdaT>
requires N1 ==Int N2

claim
<k> check => . </k>
<s> ^ a ... </s>
<impT>
  <impk>
    while (!(n <= 0)) {
      sum = sum + n;
      n = n + -1;
    }
  =>
    ?_
  </impk>
  <impstate> sum |-> 0 n |-> N1:Int => ?_ </impstate>
</impT>
<lambdaT>
  <lambdak>
    f N2:Int ~> .Map
  =>
    ?_
  </lambdak>
  <lambdaenv> f |-> 2 => ?_ </lambdaenv>
  <lambdastore>
    1 |-> muclosure(f |-> 1, lambda x. if x <= 0 then 0 else (x + (f (x + -1))))
    2 |->   closure(f |-> 1,        x, if x <= 0 then 0 else (x + (f (x + -1))))
  =>
    ?_
  </lambdastore>
  <lambdacounter> 3 => ?_ </lambdacounter>
</lambdaT>
requires N1 ==Int N2

claim
<k> check => . </k>
<s> ^ a ... </s>
<impT>
  <impk>
    while (!(n <= 0)) {
      sum = sum + n;
      n = n + -1;
    }
  =>
    ?_
  </impk>
  <impstate> sum |-> S:Int n |-> N1:Int => ?_ </impstate>
</impT>
<lambdaT>
  <lambdak>
    f (x + -1) ~> Ks:K
  =>
    ?_
  </lambdak>
  <lambdaenv> f |-> 1 x |-> L:Int => ?_ </lambdaenv>
  <lambdastore>
    1 |-> muclosure(f |-> 1, lambda x. if x <= 0 then 0 else (x + (f (x + -1))))
    2 |->   closure(f |-> 1,        x, if x <= 0 then 0 else (x + (f (x + -1))))
    L |-> N2:Int
    _:Map
  =>
    ?_
  </lambdastore>
  <lambdacounter> L +Int 1 => ?_ </lambdacounter>
</lambdaT>
requires sim(S, Ks)
 andBool N1 ==Int N2 -Int 1
 andBool isContinuation(Ks)

claim
<k> check => . </k>
<s> ^ a ... </s>
<impT>
  <impk> .K </impk>
  <impstate> sum |-> S:Int _:Map </impstate>
</impT>
<lambdaT>
  <lambdak> 0 ~> Ks:K </lambdak>
  <lambdaenv> _:Map </lambdaenv>
  <lambdastore> _:Map </lambdastore>
  <lambdacounter> _ </lambdacounter>
</lambdaT>
requires sim(S, Ks)
[trusted]

endmodule
