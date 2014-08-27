// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "k-equal.k"
module INT-SYNTAX-HOOKS
  imports #INT-INTERFACE
  syntax #Int ::= Token{[\-\+]? [0-9]+} [regex("[\\+-]?\\d+"), prefer]
  syntax Int ::= #Int
endmodule

module INT-HOOKS
  imports INT-SYNTAX-HOOKS
  imports BOOL-HOOKS
  imports K-EQUAL-HOOKS

  syntax Int ::= "~Int" Int                     [function, latex(\mathop{\sim_{\scriptstyle\it Int}}{#1}), hook(#INT:~Int_)]
               > left:
                 Int "^Int" Int                 [function, left, latex({#1}\mathrel{{\char`\^}_{\!\scriptstyle\it Int}}{#2}), hook(#INT:_^Int_)]
               > left:
                 Int "*Int" Int                 [function, left, smtlib(*), latex({#1}\mathrel{\ast_{\scriptstyle\it Int}}{#2}), hook(#INT:_*Int_)]
               /* FIXME: translate /Int and %Int into smtlib */
               /* /Int and %Int implement t-division */
               | Int "/Int" Int                 [function, left, smtlib(div), latex({#1}\mathrel{\div_{\scriptstyle\it Int}}{#2}), hook(#INT:_/Int_)]
               | Int "%Int" Int                 [function, left, smtlib(mod), latex({#1}\mathrel{\%_{\scriptstyle\it Int}}{#2}), hook(#INT:_%Int_)]
               /* divInt and modInt implement e-division */
               | Int "divInt" Int               [function, left, smtlib(div), hook(#INT:_divInt_)]
               | Int "modInt" Int               [function, left, smtlib(mod), hook(#INT:_modInt_)]
               > left:
                 Int "+Int" Int                 [function, left, smtlib(+), latex({#1}\mathrel{+_{\scriptstyle\it Int}}{#2}), hook(#INT:_+Int_)]
               | Int "-Int" Int                 [function, left, smtlib(-), latex({#1}\mathrel{-_{\scriptstyle\it Int}}{#2}), hook(#INT:_-Int_)]
               > left:
                 Int ">>Int" Int                [function, left, latex({#1}\mathrel{\gg_{\scriptstyle\it Int}}{#2}), hook(#INT:_>>Int_)]
               | Int "<<Int" Int                [function, left, latex({#1}\mathrel{\ll_{\scriptstyle\it Int}}{#2}), hook(#INT:_<<Int_)]
               > left:
                 Int "&Int" Int                 [function, left, latex({#1}\mathrel{\&_{\scriptstyle\it Int}}{#2}), hook(#INT:_&Int_)]
               > left:
                 Int "xorInt" Int               [function, left, latex({#1}\mathrel{\oplus_{\scriptstyle\it Int}}{#2}), hook(#INT:_xorInt_)]
               > left:
                 Int "|Int" Int                 [function, left, latex({#1}\mathrel{|_{\scriptstyle\it Int}}{#2}), hook(#INT:_|Int_)]
               > "minInt" "(" Int "," Int ")"   [function, smtlib(int_min), hook(#INT:minInt)]
               | "maxInt" "(" Int "," Int ")"   [function, smtlib(int_max), hook(#INT:maxInt)]
               | "absInt" "(" Int ")"           [function, smtlib(int_abs), klabel(absInt), hook(#INT:absInt)]

  rule I1:#Int divInt I2:#Int => (I1 -Int (I1 modInt I2)) /Int I2
  when I2 =/=Int 0
  rule
    I1:#Int modInt I2:#Int
  =>
    ((I1 %Int absInt(I2)) +Int absInt(I2)) %Int absInt(I2)
  when I2 =/=Int 0

  syntax Bool ::= Int "<=Int" Int         [function, left, smtlib(<=), latex({#1}\mathrel{\leq_{\scriptstyle\it Int}}{#2}), hook(#INT:_<=Int_)]
                | Int "<Int" Int          [function, left, smtlib(<), latex({#1}\mathrel{<_{\scriptstyle\it Int}}{#2}), hook(#INT:_<Int_)]
                | Int ">=Int" Int         [function, left, smtlib(>=), latex({#1}\mathrel{\geq_{\scriptstyle\it Int}}{#2}), hook(#INT:_>=Int_)]
                | Int ">Int" Int          [function, left, smtlib(>), latex({#1}\mathrel{>_{\scriptstyle\it Int}}{#2}), hook(#INT:_>Int_)]
                | Int "==Int" Int         [function, left, smtlib(=), latex({#1}\mathrel{{=}{=}_{\scriptstyle\it Int}}{#2}), hook(#INT:_==Int_)]
                | Int "=/=Int" Int        [function, left, smtlib(distinct), latex({#1}\mathrel{{=}{/}{=}_{\scriptstyle\it Int}}{#2}), hook(#INT:_=/=Int_)]
                | Int "=Int" Int          [equality, function, hook(#INT:_==Int_)]
                | Int "dividesInt" Int    [function]

  rule I1:Int =/=Int I2:Int => notBool(I1 ==Int I2)
  rule (I1:Int dividesInt I2:Int) => (I2 %Int I1) ==Int 0

  //sort Nat ::= {I:Int | I >=Int 0}
  syntax Nat
  rule isNat(I:Int) => I >=Int 0 [function, anywhere]

  syntax Int ::= freshInt(Int)    [freshGenerator, function]
  rule freshInt(I:Int) => I
endmodule
