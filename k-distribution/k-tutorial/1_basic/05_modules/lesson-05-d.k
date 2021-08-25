module LESSON-05-D-1
  syntax Boolean ::= "true" | "false"
  syntax Boolean ::= "not" Boolean [function]
endmodule

module LESSON-05-D-2
  imports LESSON-05-D-1

  rule not true => false
endmodule

module LESSON-05-D-3
  imports LESSON-05-D-1

  rule not false => true
endmodule

module LESSON-05-D
  imports LESSON-05-D-2
  imports LESSON-05-D-3
endmodule
