require "seq.k"
require "if.k"

module WHILE-SYNTAX 
  imports SEQ-SYNTAX
  imports IF-SYNTAX
  syntax K ::= "while" K "do" K
endmodule
  
module WHILE 
  imports WHILE-SYNTAX
  imports SEQ
  imports IF

  rule while E:K do S:K => if E then (S ; while E do S) else skip 
endmodule
