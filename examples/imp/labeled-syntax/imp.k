in ../../../k-prelude

kmod IMP-SYNTAX is including PL-INT + PL-ID + K

  syntax KLabel ::= +   [strict]
                  | /   [strict]
                  | <=  [seqstrict]
                  | not [strict]
                  | and [strict(1)]
                  | =   [strict(2)]
                  | ;
                  | if  [strict(1)]
                  | while
                  | list   --- "," does not work as a label, due to a Maude bug
                  | var
  syntax K ::= Id | skip
  syntax KResult ::= Bool | Int
endkm

kmod IMP-PROGRAMS is including IMP-SYNTAX
  syntax Id   ::= a | b | c | d | e | f | g | h | i | j | k | l | m
                | n | o | p | q | r | s | t | u | v | w | x | y | z
  syntax K ::= sumPgm

  macro sumPgm =
     var(list(n,,s),,
         ;(=(n,,10),,
           ;(=(s,,0),,
             while(not(<=(n,,0)),,
                   ;(=(s,,+(s,,n)),,
                     =(n,,+(n,,-1)))))))
endkm

kmod IMP-SEMANTICS is including IMP-SYNTAX
  configuration <T> <k>.K</k> <state>.Map</state> </T>
  rule <k>X:Id => I:Int<_/k> <state_>X|->I<_/state>
  rule +(I1:Int,,I2:Int) => I1 +Int I2
  rule /(I1,,I2) => I1 /Int I2  if I2 =/=Bool 0
  rule <=(I1,,I2) => I1 <=Int I2
  rule not(T:Bool) => notBool T
  rule and(true,,B:K) => B
  rule and(false,,B)  => false
  rule skip => .
  rule <k>=(X,,I) => .<_/k> <state_> X|->(_ => I) <_/state>
  rule ;(S1:K,,S2:K) => S1~>S2
  rule if(true,,S:K,,_) => S
  rule if(false,,_,,S)  => S
  rule <k>while(B,,S) => if(B,,;(S,,while(B,,S)),,skip) <_/k>
  rule <k>var(list(Kl:List{K}),,S) => S</k> <state_>. => Kl|->0 <_/state> [structural]
endkm

kmod IMP is including IMP-PROGRAMS + IMP-SEMANTICS
  syntax Bag ::= [[ KLabel ]] | pgm
  macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
  macro pgm = [['sumPgm]]
endkm
