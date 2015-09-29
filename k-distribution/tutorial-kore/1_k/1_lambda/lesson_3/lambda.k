// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "domains.k"
//require "modules/substitution.k"

module LAMBDA-COMMON
  imports BOOL-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX
  imports EMPTY-ID

  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]
  syntax Variable ::= Id
endmodule

module LAMBDA-SYNTAX
  imports LAMBDA-COMMON
  imports ID
endmodule

module LAMBDA
  imports LAMBDA-COMMON
  imports BOOL
  imports INT
  imports STRING
//  imports SUBSTITUTION

  syntax Variable   //sort declaration used by substitution hook
  syntax K ::= K "[" K "/" K "]"    [function, hook(SUBSTITUTION.userSubstitutionKore), impure]

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]

  syntax KResult ::= Val
endmodule

