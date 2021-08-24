module LESSON-02-A

  syntax Color ::= Yellow()
                 | Blue()
                 | Black()
                 | Green()
                 | colorOf(Fruit) [function]

  syntax Fruit ::= Banana() 
                 | Blueberry()
                 | Blackberry()
                 | Kiwi()

  rule colorOf(Banana()) => Yellow()
  rule colorOf(Blueberry()) => Blue()
  rule colorOf(Blackberry()) => Black()
  rule colorOf(Kiwi()) => Green()

endmodule
