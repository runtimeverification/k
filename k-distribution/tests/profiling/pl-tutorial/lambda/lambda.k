// Copyright (c) K Team. All Rights Reserved.

module KVAR-SYNTAX
  syntax KVar [hook(KVAR.KVar), token]
endmodule

module KVAR-COMMON
  imports public KVAR-SYNTAX
  imports private STRING
  syntax KVar  ::=
    "String2KVar" "(" String ")" [function, hook(STRING.string2token), klabel(String2KVar), total]
  syntax KVar  ::=
    "freshKVar" "(" Int ")" [freshGenerator, function, klabel(freshKVar), private, total]
  rule freshKVar(I:Int) => String2KVar("_" +String Int2String(I))
endmodule

module KVAR
  imports public KVAR-COMMON
endmodule

module SUBSTITUTION
  imports private MAP
  imports public KVAR
  syntax {Sort} Sort  ::=
    Sort "[" KItem "/" KItem "]" [function, hook(SUBSTITUTION.substOne), impure]
  syntax {Sort} Sort  ::=
    Sort "[" Map "]" [function, hook(SUBSTITUTION.substMany), impure]
endmodule

module LAMBDA-SYNTAX
  imports public DOMAINS-SYNTAX
  imports public KVAR-SYNTAX
  syntax Val  ::=
    KVar
  | "lambda" KVar "." Exp [binder, latex(\lambda{#1}.{#2})]
  syntax Exp  ::=
    Val
  | Exp Exp [left, strict]
  | "(" Exp ")" [bracket]
  syntax Val  ::=
    Int
  | Bool
  syntax Exp  ::=
    "-" Int
  > Exp "*" Exp [left, strict]
  | Exp "/" Exp [strict]
  > Exp "+" Exp [left, strict]
  > Exp "<=" Exp [strict]
  syntax Exp  ::=
    "if" Exp "then" Exp "else" Exp [strict(1)]
  syntax Exp  ::=
    "let" KVar "=" Exp "in" Exp [macro]
  rule let X = E in E':Exp => (lambda X . E') E
  syntax Exp  ::=
    "letrec" KVar KVar "=" Exp "in" Exp [macro]
  | "mu" KVar "." Exp [binder, latex(\mu{#1}.{#2})]
  rule letrec F:KVar X:KVar = E in E' => let F = mu F . lambda X . E in E'
endmodule

module LAMBDA
  imports public LAMBDA-SYNTAX
  imports public SUBSTITUTION
  imports public DOMAINS
  syntax KResult  ::=
    Val
  rule (lambda X:KVar . E:Exp) V:Val => E[V / X]
  rule - I => 0 -Int I
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule if true  then E else _ => E
  rule if false then _ else E => E
  rule mu X . E => E[(mu X . E) / X]
endmodule


