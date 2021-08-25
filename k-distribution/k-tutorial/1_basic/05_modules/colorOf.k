requires "fruits.k"
requires "colors.k"

module COLOROF-SYNTAX
  imports COLORS
  imports FRUITS

  syntax Color  ::= colorOf(Fruit) [function]
endmodule

module COLOROG
  imports COLOROF-SYNTAX

  rule colorOf(Banana()) => Yellow()
  rule colorOf(Blueberry()) => Blue()
endmodule
