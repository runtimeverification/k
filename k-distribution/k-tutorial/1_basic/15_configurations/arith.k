module ARITH-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX

  syntax Integer  ::= Int
                    | "(" Integer ")" [bracket]
                    > "-" Integer [seqstrict]
                    > left: Integer "*" Integer [seqstrict]
                    | Integer "/" Integer [seqstrict]
                    > left: Integer "+" Integer [seqstrict]
                    | Integer "-" Integer [seqstrict]

  syntax Stmt       ::= Integer
                    | Bool ";" Stmt
                    | "reset" ";" Stmt
endmodule

module ARITH
  imports INT
  imports ARITH-SYNTAX
  imports BOOL

  configuration <T>
                  <k> $PGM:K </k>
                  <state>
                    <div> false </div>
                  </state>
                </T>

  syntax Bool ::= isKResult(Integer) [function, symbol]

  rule  <k> - N => 0 -Int N ...</k>
  rule  <k> N * M => N *Int M ...</k>
  rule  <k> N + M => N +Int M ...</k>
  rule  <k> N - M => N -Int M ...</k>

  rule  <k> N / M => N /Int M ...</k> 
        <div> false </div>  requires M =/=Int 0

  rule  <k> N / M => N divInt M ...</k>
        <div> true </div>   requires M =/=Int 0

  rule  <k> B ; S => S </k>
        <div> _ => B </div>

  rule  <k> reset ; E => E </k>
        (_:StateCell => <state> .Bag ...</state>)

  rule isKResult(_:Int) => true
  rule isKResult(_) => false [owise]
endmodule
