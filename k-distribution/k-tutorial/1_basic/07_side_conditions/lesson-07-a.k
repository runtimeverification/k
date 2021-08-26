module LESSON-07-A
  imports BOOL
  imports INT

  syntax Bool  ::= isEven(Int) [function]

  rule isEven(N) => true requires N %Int 2 ==Int 0
  rule isEven(_) => false [owise]
endmodule
