module LESSON-06-A
  imports BOOL

  syntax Fruit  ::= Blueberry() | Banana()
  syntax Bool   ::= isBlue(Fruit) [function]

  rule isBlue(Blueberry()) => true
  rule isBlue(Banana()) => false
endmodule
