module VERIFICATION

imports MAIN

endmodule

module SYNC-POINT-CANDIDATES

imports MAIN

syntax Id ::= "x" [token]
            | "y" [token]

claim
<s> ~ a => ^ b ... </s>
<impk> _:Int </impk>
[trusted]

claim
<s> ~ b => ^ a ... </s>
<lambdak> _:Int </lambdak>
[trusted]

endmodule

module SIMPLE-SPEC

imports VERIFICATION
imports SYNC-POINT-CANDIDATES

claim
<k> check => . </k>
<s> ^ a ... </s>
<impT>
  <impk> addi(x,y) => ?_ </impk>
  <impstate> ... x |-> N1:Int y |-> M1:Int ... </impstate>
</impT>
<lambdaT>
  <lambdak> addl(x,y) => ?_ </lambdak>
  <lambdaenv> ... x |-> Lx:Int y |-> Ly:Int ... </lambdaenv>
  <lambdastore> ... Lx |-> N2:Int Ly |-> M2:Int ... </lambdastore>
  <lambdacounter> _ </lambdacounter>
</lambdaT>
requires N1 ==Int N2
 andBool M1 ==Int M2
 andBool ?_Ks1 ==K ?_Ks2

claim
<k> check => . </k>
<s> ^ a ... </s>
<impT>
  <impk> I1:Int </impk>
  <impstate> _:Map </impstate>
</impT>
<lambdaT>
  <lambdak> I2:Int </lambdak>
  <lambdaenv> _:Map </lambdaenv>
  <lambdastore> _:Map </lambdastore>
  <lambdacounter> _ </lambdacounter>
</lambdaT>
requires I1 ==Int I2
[trusted]

endmodule
