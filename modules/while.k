require seq
require if

kmod WHILE is including SEQ + IF
  syntax K ::= while K do K
  
  rule <k> while E:K do S:K => if E then (S ; while E do S) else skip <_/k>
endkm
