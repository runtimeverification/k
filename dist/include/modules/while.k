require "seq.k"
require "if.k"

module WHILE
  imports SEQ
  imports IF
  syntax K ::= "while" K "do" K
  
  rule <k> while E:K do S:K => if E then (S ; while E do S) else skip ...</k>
endmodule
