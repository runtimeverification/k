// Copyright (c) 2012-2014 K Team. All Rights Reserved.

module LAMBDA
  syntax K ::= K "[" K "/" K "]" [hook(Substitution:userSubstitution)]

  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder]
  syntax KResult ::= Val


  syntax Exp ::= Val
               | Exp Exp              [left, strict]
               | "(" Exp ")"          [bracket]

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]
endmodule
