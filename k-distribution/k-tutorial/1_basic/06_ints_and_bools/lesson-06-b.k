requires "lesson-06-a.k"

module LESSON-06-B
  imports LESSON-06-A

  syntax Fruit  ::= Gross()

  syntax Bool ::= isYellow(Fruit) [function]
                | isBlueOrYellow(Fruit) [function]
                | isBlueAndNotYellow(Fruit) [function]

  rule isYellow(Banana()) => true
  rule isYellow(Blueberry()) => false

  rule isBlue(Gross()) => true
  rule isYellow(Gross()) => true

  rule isBlueOrYellow(F) => isBlue(F) orBool isYellow(F)

  rule isBlueAndNotYellow(F) => isBlue(F) andBool (notBool isYellow(F))
endmodule
