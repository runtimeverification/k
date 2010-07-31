in ../../../k-prelude

kmod IMP-SYNTAX is including PL-INT + PL-ID + K

  syntax KLabel ::= +   [strict]
                  | /   [strict]
                  | <=  [seqstrict]
                  | not [strict]
                  | and [strict(1)]
                  | skip
                  | =   [strict(2)]
                  | ;
                  | if  [strict(1)]
                  | while
                  | list   --- "," does not work as a label, due to a Maude bug
                  | var
                  | Id

  syntax KResultLabel ::= Bool | Int
endkm

kmod IMP-PROGRAMS is including IMP-SYNTAX
  syntax Id   ::= a | b | c | d | e | f | g | h | i | j | k | l | m
                | n | o | p | q | r | s | t | u | v | w | x | y | z
  syntax K ::= sumPgm

  macro sumPgm =
     var(list(n(.List{K}),,s(.List{K})),,
         ;(=(n(.List{K}),,10(.List{K})),,
           ;(=(s(.List{K}),,0(.List{K})),,
             while(not(<=(n(.List{K}),,0(.List{K}))),,
                   ;(=(s(.List{K}),,+(s(.List{K}),,n(.List{K}))),,
                     =(n(.List{K}),,+(n(.List{K}),,-1(.List{K}))))))))
endkm

kmod IMP-SEMANTICS is including IMP-SYNTAX
  configuration <T> <k>.K</k> <state>.Map</state> </T>
  rule <k>X:Id(.List{K}) => I:Int(.List{K})<_/k> <state_>X(.List{K})|->I(.List{K})<_/state>
  rule +(I1:Int(.List{K}),,I2:Int(.List{K})) => (I1 +Int I2)(.List{K})
  rule /(I1(.List{K}),,I2(.List{K})) => (I1 /Int I2)(.List{K})  if I2 =/=Bool 0
  rule <=(I1(.List{K}),,I2(.List{K})) => (I1 <=Int I2)(.List{K})
  rule not(T:Bool(.List{K})) => (notBool T)(.List{K})
  rule and(true(.List{K}),,B:K) => B
  rule and(false(.List{K}),,B)  => false(.List{K})
  rule skip(.List{K}) => .
  rule <k>=(X(.List{K}),,I(.List{K})) => .<_/k> <state_> X(.List{K})|->(_ => I(.List{K})) <_/state>
  rule ;(S1:K,,S2:K) => S1~>S2
  rule if(true(.List{K}),,S:K,,_) => S
  rule if(false(.List{K}),,_,,S)  => S
  rule <k>while(B,,S) => if(B,,;(S,,while(B,,S)),,skip(.List{K})) <_/k>
  rule <k>var(list(Kl:List{K}),,S) => S</k> <state_>. => Kl|->0(.List{K}) <_/state> [structural]
endkm

kmod IMP is including IMP-PROGRAMS + IMP-SEMANTICS
  syntax Bag ::= [[ KLabel ]] | pgm
  macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>
  macro pgm = [['sumPgm]]
endkm
