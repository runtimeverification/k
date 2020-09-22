module MAIN-SPEC

imports MAIN

claim
<k> check => . </k>
<s> ^ a ... </s>
<aT>
  <ak> beginA() => ?_:KItem ... </ak>
  <am> .IMap => ?_ </am>
</aT>
<bT>
  <bk> beginB() => ?_:KItem ... </bk>
  <bm> .IMap => ?_ </bm>
</bT>

claim
<k> check => . </k>
<s> ^ a ... </s>
<aT>
  <ak> loopA(I1,N1) => ?_:KItem ... </ak>
  <am> M1:IMap => ?_ </am>
</aT>
<bT>
  <bk> loopB(I2,N2) => ?_:KItem ... </bk>
  <bm> M2:IMap => ?_ </bm>
</bT>
requires simS(M1,M2)
 andBool I1 ==Int I2
 andBool N1 ==Int N2
 andBool I1 ==Int 0
 andBool N1 >=Int 1

claim
<k> check => . </k>
<s> ^ a ... </s>
<aT>
  <ak> loopA(I1,N1) => ?_:KItem ... </ak>
  <am> M1:IMap => ?_ </am>
</aT>
<bT>
  <bk> loopB(I2,N2) => ?_:KItem ... </bk>
  <bm> M2:IMap => ?_ </bm>
</bT>
requires simS(M1,M2)
 andBool I1 ==Int I2
 andBool N1 ==Int N2
 andBool I1 >=Int 1
 andBool N1 >=Int 1

claim
<k> check => . </k>
<s> ^ a ... </s>
<aT>
  <ak> endA() ... </ak>
  <am> M1:IMap </am>
</aT>
<bT>
  <bk> endB() ... </bk>
  <bm> M2:IMap </bm>
</bT>
requires simS(M1,M2)
[trusted]

endmodule
