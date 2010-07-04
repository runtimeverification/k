kmod IMP is including EXP
  syntax K ::= K ; K                  [prec 100 gather(e E) strict(1)]
             | while K do K
  syntax KResult ::= skip
  
  rule V:KResult ; S:K => S
  rule <k> while E:K do S => if E then (S ; while E do S) else skip <_/k>
endkm