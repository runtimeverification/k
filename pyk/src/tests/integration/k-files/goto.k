// Copyright (c) 2014-2019 K Team. All Rights Reserved.

module GOTO-SYNTAX
  imports BOOL-SYNTAX
  imports K-EQUAL-SYNTAX
  imports INT

  syntax OpCode ::= "PUSH" Int
                  | "POP"
                  | "ADD"
                  | "SUB"
                  | "DUP0"
                  | "DUP1"
                  | "SWAP"
                  | "RETURN"
                  | "GT"
                  | "JUMP" Int
                  | "JUMPI" Int [symbol(jumpi)]

  syntax Stack ::= ".Stack" | Int ":" Stack [symbol(ws)]

  syntax Int ::= Int "<Word" Int [function, total]
  rule I1 <Word I2 => #if I1 <Int I2 #then 1 #else 0 #fi

endmodule

module GOTO
  imports GOTO-SYNTAX
  imports BOOL
  imports INT
  imports MAP
  imports SET
  imports BASIC-K

  syntax KItem ::= OpCode

  configuration <goto>
                  <k> $PGM:KItem </k>
                  <pc> 0 </pc>
                  <pgm> .Map </pgm>
                  <stack> .Stack </stack>
                  <return> 0 </return>
                </goto>

  rule <k> .K => OP </k> <pc> PC => PC +Int 1 </pc> <pgm> ... PC |-> OP ... </pgm>

  rule <k> PUSH  I => .K ... </k> <stack> WS => I : WS </stack>
  rule <k> POP     => .K ... </k> <stack> _ : WS => WS </stack>
  rule <k> ADD     => .K ... </k> <stack> I1 : I2 : WS => I1 +Int I2 : WS </stack>
  rule <k> SUB     => .K ... </k> <stack> I1 : I2 : WS => I1 -Int I2 : WS </stack>
  rule <k> DUP0    => .K ... </k> <stack> I1 : WS => I1 : I1 : WS </stack>
  rule <k> DUP1    => .K ... </k> <stack> I1 : I2 : WS => I2 : I1 : I2 : WS </stack>
  rule <k> SWAP    => .K ... </k> <stack> I1 : I2 : WS => I2 : I1 : WS </stack>
  rule <k> GT      => .K ... </k> <stack> I1 : I2 : WS => I2 <Word I1 : WS </stack>
  rule <k> JUMP  I => .K ... </k> <pc> _ => I </pc>
  rule <k> RETURN  => .K ... </k> <stack> I : WS => WS </stack> <return> _ => I </return>

  rule [jumpi.true]:  <k> JUMPI I => JUMP I ... </k> <stack> W : WS => WS </stack> requires W =/=Int 0
  rule [jumpi.false]: <k> JUMPI _ => .K     ... </k> <stack> _ : WS => WS </stack> [owise]

endmodule

module GOTO-SPEC
  imports GOTO

  claim [sum-n]:
        <k> .K </k>
        <pc> 1 => ?_ </pc>
        <stack> .Stack => ?_ </stack>
        <return> 0 => ?S </return>
        <pgm>
          1  |-> PUSH 0
          2  |-> PUSH N:Int
          3  |-> DUP0
          4  |-> PUSH 0
          5  |-> GT
          6  |-> JUMPI 15
          7  |-> SWAP
          8  |-> DUP1
          9  |-> ADD
          10 |-> SWAP
          11 |-> PUSH 1
          12 |-> SWAP
          13 |-> SUB
          14 |-> JUMP 3
          15 |-> SWAP
          16 |-> RETURN
        </pgm>
   requires 0 <=Int N
    ensures ?S ==Int (N *Int (N +Int 1)) /Int 2

endmodule
