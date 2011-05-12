kmod SEQ is including K
  syntax K ::= K ; K                  [prec 100 gather(e E) strict(1)]
  syntax KResult ::= skip
  
  rule V:KResult ; S:K => S [structural]
endkm
