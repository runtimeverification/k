requires "arith.k"

module BOOLS-SYNTAX
  imports BOOL-SYNTAX
  imports ARITH-SYNTAX

  syntax Bool   ::= "(" Bool ")" [bracket]
                  > "!" Bool [function]
                  > left: Bool "&&" Bool [function]
                  > left: Bool "^" Bool [function]
                  > left: Bool "||" Bool [function]
                  > right: Bool "->" Bool [function]

  syntax Bool   ::= Integer "<"  Integer [function]
                  | Integer "<=" Integer [function]
                  | Integer ">"  Integer [function]
                  | Integer ">=" Integer [function]
                  | Integer "==" Integer [function]
                  | Integer "!=" Integer [function]
endmodule

module BOOLS
  imports ARITH
  imports BOOLS-SYNTAX
  imports BOOL

  rule ! B => notBool B
  rule A && B => A andBool B
  rule A ^ B => A xorBool B
  rule A || B => A orBool B
  rule A -> B => A impliesBool B

  rule N < M => N <Int M
  rule N <= M => N <=Int M
  rule N > M => N >Int M
  rule N >= M => N >=Int M
  rule N == M => N ==Int M
  rule N != M => N =/=Int M
endmodule
