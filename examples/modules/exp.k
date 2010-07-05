kmod EXP is including PL-INT + K
--- Basic arithmetic and boolean operations;
  syntax K ::= K + K   [gather(E e) prec 33 strict]       --- addition
             | K * K   [gather(E e) prec 31 strict]       --- multiplication
             | K / K   [gather(E e) prec 31 strict]       --- division
             | K <= K  [prec 37 latex "{#1}\leq{#2}" seqstrict]
             | K == K  [prec 37 strict]                   --- equality test
             | not K     [prec 53 strict]                   --- boolean negation
             | K and K [gather(E e) prec 55 strict(1)]    --- boolean conjunction
             | if K then K else K   [strict(1)]
  syntax KResult ::= Bool | Int 

  rule  I1:Int + I2:Int => I1 +Int I2  
--- following rules for _*_ need to be written like that because of 
--- parsing ambiguities: a*b can also be seen as __(a,*b) ...
  rule  _*_(I1,I2) => I1 *Int I2 
  rule  I1 / I2 => I1 /Int I2  if I2 =/=Bool 0 
  rule  I1 <= I2 => I1 <=Int I2  
  rule  V1:KResult == V2:KResult => V1 ==Bool V2
  rule  not T:Bool => notBool T
  rule  true and E:K => E
  rule  false and E => false
  rule if true then E else _ => E
  rule if false then _ else E => E
endkm