requires "a-prime.k"
requires "b-prime.k"

module MAIN-SYNTAX

endmodule

module MAIN

imports MAIN-SYNTAX

imports A
imports B

imports BOOL
imports INT
imports STRING

imports STRATEGY
imports RULE-TAG-SYNTAX
imports K-REFLECTION

configuration <c>
  <k> $PGM:Pgm </k>
  <s/>
  <aT/>
  <bT/>
</c>

syntax Bool ::= isSyncPoint(#RuleTag, String) [function]

rule isSyncPoint(a, Lbl)
    => Lbl ==String "beginA"
orBool Lbl ==String "loopA"
orBool Lbl ==String "endA"

rule isSyncPoint(b, Lbl)
    => Lbl ==String "beginB"
orBool Lbl ==String "loopB"
orBool Lbl ==String "endB"

rule <s> ~ a => #if isSyncPoint(a, #getKLabelString(K))
                #then ^ b
                #else ^ a
                #fi ... </s>
     <ak> K:PgmA ... </ak>

rule <s> ~ b => #if isSyncPoint(b, #getKLabelString(K))
                #then ^ a
                #else ^ b
                #fi ... </s>
     <bk> K:PgmB ... </bk>

syntax String ::= RuleTag2String ( #RuleTag ) [function, hook(STRING.token2string)]

rule <s> ~ RT:#RuleTag => . ... </s>
     requires RuleTag2String(RT) =/=String "a"
      andBool RuleTag2String(RT) =/=String "b"

syntax Pgm ::= "check"

/*
rule <k> check => . ... </k>
<aT>
  <ak> KA:PgmA </ak>
  <am> SA:IMap </am>
</aT>
<bT>
  <bk> KB:PgmB </bk>
  <bm> SB:IMap </bm>
</bT>
requires simC(KA,KB)
 andBool simS(SA,SB)
 [tag(ck)]

syntax Bool ::= simC(PgmA, PgmB) [function]
rule simC(beginA(), beginB()) => true
rule simC(loopA(I1, N1), loopB(I2, N2)) => true
    requires I1 ==Int I2
     andBool N1 ==Int N2
rule simC(endA(), endB()) => true
*/

syntax Bool ::= simS(IMap, IMap) [function, smtlib(simS)]
rule simS(M, M) => true
rule simS(M1[K1 <- V1], M2[K2 <- V2]) => true
    requires simS(M1, M2)
     andBool simK(K1, K2)
     andBool simV(V1, V2)

syntax Bool ::= simK(Int, Int) [function, smtlib(simK)]
rule simK(I1, loc(0, I2)) => true
    requires I1 ==Int I2

syntax Bool ::= simV(Int, Int) [function, smtlib(simV)]
rule simV(hash(V1), sha256(V2)) => true
    requires simV(V1, V2)
rule simV(M1[K1], M2[K2]) => true
    requires simS(M1, M2)
     andBool simK(K1, K2)

endmodule
