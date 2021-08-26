module ARITH-SYNTAX
  imports INT-SYNTAX
  syntax Integer  ::= Int
                    | "(" Integer ")" [bracket]
                    > "-" Integer [seqstrict]
                    > left: Integer "*" Integer [seqstrict]
                    | Integer "/" Integer [seqstrict]
                    > left: Integer "+" Integer [seqstrict]
                    | Integer "-" Integer [seqstrict]
endmodule

module ARITH
  imports INT
  imports ARITH-SYNTAX
  imports BOOL

  syntax Bool ::= isKResult(Integer) [function, symbol]

  rule <k> - N => 0 -Int N ...</k>
  rule <k> N * M => N *Int M ...</k>
  rule <k> N / M => N /Int M ...</k> requires M =/=Int 0
  rule <k> N + M => N +Int M ...</k>
  rule <k> N - M => N -Int M ...</k>

  rule isKResult(_:Int) => true
  rule isKResult(_) => false [owise]
endmodule
