// Copyright (c) 2014-2019 K Team. All Rights Reserved.

module IMP-SYNTAX
  imports BOOL-SYNTAX
  imports INT-SYNTAX
  imports ID

  syntax AExp  ::= Int | Id
                 | AExp "*" AExp              [symbol(_*_), left, seqstrict, color(pink)]
                 | AExp "/" AExp              [symbol(_/_), left, seqstrict, color(pink)]
                 | AExp "%" AExp              [symbol(_%_), left, seqstrict, color(pink)]
                 > AExp "+" AExp              [symbol(_+_), left, seqstrict, color(pink)]
                 | AExp "-" AExp              [symbol(_-_), left, seqstrict, color(pink)]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<" AExp              [symbol(_<_), seqstrict, color(pink)]
                 | AExp "<=" AExp             [symbol(_<=_), seqstrict, color(pink)]
                 | "!" BExp                   [symbol(!_), strict, color(pink)]
                 > BExp "&&" BExp             [symbol(_&&_), left, strict(1), color(pink)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"                    [symbol({})]
                 | "{" Stmt "}"               [symbol({_}), format(%1%i%n%2%d%n%3)]
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [symbol(_=_;), strict(2), color(pink), format(%1 %2 %3%4)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [symbol(if(_)_else_), strict(1), colors(yellow, white, white, yellow), format(%1 %2%3%4 %5 %6 %7)]
                 | "while" "(" BExp ")" Block [symbol(while(_)_), colors(yellow,white,white), format(%1 %2%3%4 %5)]
                 > Stmt Stmt                  [symbol(__), left, format(%1%n%2)]

  syntax Pgm ::= "int" Ids ";" Stmt           [symbol(int_;_), format(%1 %2%3%n%4), colors(yellow,pink)]
  syntax Ids ::= List{Id,","}                 [symbol(_,_), format(%1%2 %3)]
endmodule

module IMP
  imports IMP-SYNTAX
  imports BOOL
  imports INT
  imports MAP
  imports SET
  imports BASIC-K

  syntax KResult ::= Int | Bool
  syntax KItem   ::= Pgm

  syntax KItem ::= Error(Id, Map)
  syntax KItem ::= #lookup(Id, Map) [function, total]

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red"> .Map </state>
                </T>

  rule #lookup(X, M) => M[X] requires X in_keys(M)
  rule #lookup(X, M) => Error(X, M) [owise]

  rule <k> I1 * I2 => I1 *Int I2   ... </k>
  rule <k> I1 / I2 => I1 /Int I2   ... </k> requires I2 =/=Int 0
  rule <k> I1 % I2 => I1 modInt I2 ... </k> requires I2 =/=Int 0
  rule <k> I1 + I2 => I1 +Int I2   ... </k>
  rule <k> I1 - I2 => I1 -Int I2   ... </k>

  rule <k> I1 < I2    => I1 <Int I2  ... </k>
  rule <k> I1 <= I2   => I1 <=Int I2 ... </k>
  rule <k> ! T        => notBool T   ... </k>
  rule <k> true && B  => B           ... </k>
  rule <k> false && _ => false       ... </k>

  rule [var]: <k> X:Id => #lookup(X, STATE) ... </k> <state> STATE </state>

  rule [block]: <k> {S} => S  ... </k>
  rule [block-empty]: <k> {}  => .K ... </k>

  rule [assign]: <k> X = I:Int; => .K ... </k> <state> STATE => STATE [ X <- I ] </state>

  rule [sequence]: <k> S1:Stmt S2:Stmt => S1 ~> S2 ... </k>

  rule [if-true]: <k> if (true)  S else _ => S ... </k>
  rule [if-false]: <k> if (false) _ else S => S ... </k>

  rule [while]: <k> while (B) S => if (B) {S while (B) S} else {} ... </k>

  rule [decl]: <k> int (X , Xs => Xs) ; _ ... </k> <state> STATE => STATE [ X <- 0 ] </state>
    requires notBool (X in keys(STATE))

  rule [decl-empty]: <k> int .Ids ; S => S ... </k>
endmodule
