module LESSON-06-C-SYNTAX
  imports BOOL-SYNTAX

  syntax Bool   ::= "(" Bool ")" [bracket]
                  > "!" Bool [function]
                  > left: Bool "&&" Bool [function]
                  > left: Bool "^" Bool [function]
                  > left: Bool "||" Bool [function]
                  > right: Bool "->" Bool [function]
endmodule

module LESSON-06-C
  imports LESSON-06-C-SYNTAX
  imports BOOL

  rule ! B => notBool B
  rule A && B => A andBool B
  rule A ^ B => A xorBool B
  rule A || B => A orBool B
  rule A -> B => A impliesBool B
endmodule
