// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "kast.k"
require "misc.k"

module TEST-PROGRAMS
  import TEST
  import ID
endmodule

module TEST
  import BASIC-K
  import STRICTNESS
  import BOOL
  import LOGIC
  import INT
  import EMPTY-ID
  import MAP
  import K-RESULT

  syntax AExp ::= Int
  syntax AExp ::= Id
  syntax AExp ::= AExp "+" AExp     [klabel('_+_), strict, left]
  syntax AExp ::= AExp "/" AExp     [klabel('_/_), strict, left]
  syntax AExp ::= "(" AExp ")"      [bracket]

  syntax BExp ::= Bool
  syntax BExp ::= AExp "<=" AExp    [klabel('_<=_), strict]
  syntax BExp ::= "!" BExp          [klabel('!_), strict]
  syntax BExp ::= BExp "&&" BExp    [klabel('_&&_), strict(1), left]
  syntax BExp ::= "(" BExp ")"      [bracket]

  syntax Block ::= "{" "}"          [klabel('empty-block)]
  syntax Block ::= "{" Stmt "}"     [klabel('block_)]

  syntax Stmt ::= Block
  syntax Stmt ::= Id "=" AExp ";"                           [klabel('_=_;), strict(2)]
  syntax Stmt ::= "if" "(" BExp ")" Block "else" Block      [klabel('if__else_), strict(1)]
  syntax Stmt ::= "while" "(" BExp ")" Block                [klabel('while__)]
  syntax Stmt ::= Stmt Stmt                                 [klabel('__), left]

  syntax Pgm ::= "int" Ids ";" Stmt     [klabel('int_;_)]

  syntax Ids ::= List{Id, ","}

  syntax priority '_/_ > '_+_
  syntax priority '!_ > '_&&_

  configuration
    <top>
      <k> $PGM:Pgm </k>
      <state> .Map </state>
    </top>

  syntax KResult ::= Bool
  syntax KResult ::= Int
  syntax KBool ::= "isStmt" "(" K ")"                   [klabel(isStmt), function]

  rule while(BE) S => if(BE) { S while (BE) S } else {}

  rule {} => .::K
  rule { S } => S requires isStmt(S)

  rule <k> `X => I::Int` ...</k> <state> X |-> I ...</state> requires isId(X)
  rule <k> X = I; => .::K ...</k> <state> X |-> `_ => I` ...</state> requires isId(X) andBool isInt(I)

  rule A <= B => true requires isInt(A) andBool isInt(B) andBool A <=Int B
  rule A <= B => false requires isInt(A) andBool isInt(B) andBool notBool(A <=Int B)
  rule A + B => A +Int B requires isInt(A) andBool isInt(B)

  rule if(true) S1 else S2 => S1
  rule if(false) S1 else S2 => S2

  // todo: Radu, check why the extra cast is needed
  rule `__`(S1::Stmt, S2::Stmt) => S1 ~> S2 requires isStmt(S1) andBool isStmt(S2)

endmodule
