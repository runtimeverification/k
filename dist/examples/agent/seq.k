module SEQ-SYNTAX
  syntax K ::= "skip"
             >  K ";" K                  [left, strict(1)]
endmodule
  
module SEQ
  imports SEQ-SYNTAX
  syntax KResult ::= "skip"
  rule V:KResult ; S:K => S [structural]
endmodule
