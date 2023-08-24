// Copyright (c) K Team. All Rights Reserved.

module IMP-SYNTAX
  imports public BOOL-SYNTAX
  imports public INT-SYNTAX
  imports public ID
  syntax AExp  ::=
    Int
  | Id
  | AExp "/" AExp [color(pink), klabel(_/_), left, seqstrict, symbol]
  > AExp "+" AExp [color(pink), klabel(_+_), left, seqstrict, symbol]
  | "(" AExp ")" [bracket]
  syntax BExp  ::=
    Bool
  | AExp "<=" AExp [color(pink), klabel(_<=_), latex({#1}\leq{#2}), seqstrict, symbol]
  | "!" BExp [color(pink), klabel(!_), strict, symbol]
  > BExp "&&" BExp [color(pink), klabel(_&&_), left, strict(1), symbol]
  | "(" BExp ")" [bracket]
  syntax Block  ::=
    "{" "}" [klabel({}), symbol]
  | "{" Stmt "}" [format(%1%i%n%2%d%n%3), klabel({_}), symbol]
  syntax Stmt  ::=
    Block
  | Id "=" AExp ";" [color(pink), format(%1 %2 %3%4), klabel(_=_;), strict(2), symbol]
  | "if" "(" BExp ")" Block "else" Block [colors(yellow, white, white, yellow), format(%1 %2%3%4 %5 %6 %7), klabel(if(_)_else_), strict(1), symbol]
  | "while" "(" BExp ")" Block [colors(yellow,white,white), format(%1 %2%3%4 %5), klabel(while(_)_), symbol]
  > Stmt Stmt [format(%1%n%2), klabel(__), left, symbol]
  syntax Pgm  ::=
    "int" Ids ";" Stmt [colors(yellow,pink), format(%1 %2%3%n%4), klabel(int_;_), symbol]
  syntax Ids  ::=
    List{Id,","} [format(%1%2 %3), klabel(_,_), symbol]
endmodule

module IMP
  imports public IMP-SYNTAX
  imports public BOOL
  imports public INT
  imports public MAP
  imports public SET
  imports public BASIC-K
  syntax KResult  ::=
    Int
  | Bool
  syntax KItem  ::=
    Pgm
  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                </T>
  rule <k> X:Id => STATE[X] ... </k> <state> STATE </state> requires X in_keys(STATE)
  rule <k> I1 / I2 => I1 /Int I2 ... </k>  requires I2 =/=Int 0
  rule <k> I1 + I2 => I1 +Int I2 ... </k>
  rule <k> I1 <= I2   => I1 <=Int I2 ... </k>
  rule <k> ! T        => notBool T   ... </k>
  rule <k> true && B  => B           ... </k>
  rule <k> false && _ => false       ... </k>
  rule <k> {}  => . ... </k>
  rule <k> {S} => S ... </k>
  rule <k> X = I:Int; => . ... </k> <state> STATE => STATE [ X <- I ] </state>
  rule <k> S1:Stmt S2:Stmt => S1 ~> S2 ... </k>
  rule <k> if (true)  S else _ => S ... </k>
  rule <k> if (false) _ else S => S ... </k>
  rule [while]: <k> while (B) S => if (B) {S while (B) S} else {} ... </k>
  rule <k> int (X , Xs => Xs) ; _ ... </k> <state> STATE => STATE [ X <- 0 ] </state>
    requires notBool (X in keys(STATE))
  rule <k> int .Ids ; S => S ... </k>
endmodule
