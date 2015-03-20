// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "thekstuff.k"

module TEST
  import THEKSTUFF

  syntax KResult

//  syntax Id ::= Token{[A-Za-z\_][A-Za-z0-9\_]*}     [notInRules, regex("(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*")]

  syntax Bool ::= "true"           [klabel(_andBool_), function, hook(#BOOL:_andBool_)]
  syntax Bool ::= "false"          [klabel(_orBool_), function, hook(#BOOL:_orBool_)]
  syntax Int ::= r"[\\+-]?\\d+"    [prefer]
  syntax Id

  syntax Bool ::= "notBool" "(" Bool ")"    [klabel(notBool_),  function, hook(#BOOL:notBool_)]
  syntax Bool ::= Bool "andBool" Bool       [klabel('_andBool_), function, hook(#BOOL:_andBool_), left]

  syntax Bool ::= K "==K" K                 [klabel('_==K_),  function, hook(#K-EQUAL:_==K_), left]
  syntax Bool ::= K "=/=K" K                [klabel('_=/=K_), function, hook(#K-EQUAL:_=/=K_), left]

  syntax priority '_==K_ '_=/=K_ > 'notBool_ > '_andBool_

  syntax Int ::= Int "+Int" Int     [klabel('_+Int_), function, hook(#INT:_+Int_), left]
  syntax Int ::= Int "-Int" Int     [klabel('_-Int_), function, hook(#INT:_-Int_), left]
  syntax Int ::= Int "*Int" Int     [klabel('_*Int_), function, hook(#INT:_*Int_), left]
  syntax Int ::= Int "/Int" Int     [klabel('_/Int_), function, hook(#INT:_/Int_), left]
  syntax Int ::= Int "%Int" Int     [klabel('_%Int_), function, hook(#INT:_%Int_), left]

  syntax Bool ::= Int "<=Int" Int       [klabel('_<=Int_), function, hook(#INT:_<=Int_), left]
  syntax Bool ::= Int "<Int" Int        [klabel('_<Int_),  function, hook(#INT:_<Int_),  left]
  syntax Bool ::= Int ">=Int" Int       [klabel('_>=Int_), function, hook(#INT:_>=Int_), left]
  syntax Bool ::= Int ">Int" Int        [klabel('_>Int_),  function, hook(#INT:_>Int_),  left]

  syntax priority '_*Int_ '_/Int_ '_%Int_ > '_+Int_ '_-Int_

  syntax Int ::= "freshInt" "(" Int ")" [klabel('freshInt), function, freshGenerator]
//  rule 'freshInt(I:Int) => I:Int


  syntax Map ::= Map Map        [klabel('_Map_), function, hook(Map:__)]
  syntax Map ::= ".Map"         [klabel('_Map_),  function, hook(Map:.Map)]
  syntax Map ::= Id "|->" Int   [klabel('_|->_), function, hook(Map:_|->_)]
  syntax priorities '_|->_ > '_Map_

  syntax Set ::= "keys" "(" Map ")"     [klabel('keys), function, hook(Map:keys)]
  syntax Bool ::= K "in" Set            [klabel('_in_), function, hook(Set:in)]


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

  syntax KCell ::= "<k>" K "</k>"                       [klabel(<k>),       maincell]
  syntax KCell ::= "initKCell"                          [klabel(initKCell), initializer]
  syntax StateCell ::= "<state>" Map "</state>"         [klabel(<state>),       cell]
  syntax StateCell ::= "initStateCell"                  [klabel(initStateCell), initializer]
  syntax TopCell ::= "<top>" KCell StateCell "</top>"   [klabel(<top>), cell]
  syntax TopCell ::= "initTopCell"                      [klabel(initThread), initializer]


  syntax KResult ::= Bool
  syntax KResult ::= Int
  syntax Bool ::= "isKResult" "(" K ")"     [klabel(isKResult), function]
  syntax Bool ::= "isInt" "(" K ")"         [klabel(isKResult), function]
  syntax Bool ::= "isStmt" "(" K ")"         [klabel(isStmt), function]
  syntax Bool ::= "isId" "(" K ")"         [klabel(isId), function]

  rule <top><k> `while(BE) S => if(BE) { S while (BE) S } else {}` ~> R </k> SC </top>

  rule <top><k> `{} => .::K` ~> R </k> SC </top>
  rule <top><k> `{ S } => S` ~> R </k> SC </top> requires isStmt(S)

  rule <top><k> `X => I::Int` ~> R </k> <state> X |-> I M </state> </top> requires isId(X)
  rule <top><k> `X = I; => .::K` ~> R </k> <state> X |-> `_ => I` M </state> </top> requires isId(X) andBool isInt(I)

  rule <top><k> `A <= B => A <=Int B` ~> R </k> SC </top> requires isInt(A) andBool isInt(B)
  rule <top><k> `A + B => A +Int B` ~> R </k> SC </top> requires isInt(A) andBool isInt(B)

  rule <top><k> `if(true) S1 else S2 => S1` ~> R </k> SC </top>
  rule <top><k> `if(false) S1 else S2 => S2` ~> R </k> SC </top>

  // todo: Radu, check why the extra cast is needed
  rule <top><k> ``__`(S1::Stmt, S2::Stmt) => S1 ~> S2` ~> R </k> SC </top> requires isStmt(S1) andBool isStmt(S2)

endmodule
