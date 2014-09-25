// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "modules/unification.k"

module LOGIK-SYNTAX
  syntax Term ::= Variable
                | Int
                | String
                | "(" Term ")"                                   [bracket]
                | OperationName
                | OperationName "(" Terms ")"                    [strict(2)]
                > Term "*" Term                                  [strict,left]
                > left:
                  Term "+" Term                                  [strict]
                | Term "-" Term                                  [strict]
                | "[" Terms "]"                                  [strict]
                | "[" Terms "|" Term "]"
  syntax Terms ::= List{Term,","}

  syntax Predicate ::= Bool
                     | PredicateName
                     | PredicateName "(" Terms ")"
                     > Term "<=" Term                            [strict]
                     | Term ">"  Term                            [strict]
                     | Term "is" Term                            [strict(2)]
                     | "write" "(" Term ")"                      [strict]

  syntax Predicates ::= List{Predicate,","}

  syntax Clause ::= Predicate ":-" Predicates "."
                 | Predicate "."
  syntax Query ::= "?-" Predicates "."
  syntax Pgm ::= Query | Clause Pgm

  syntax Variable      ::= Token{[\_A-Z][a-zA-Z0-9\_]*}          [notInRules]
  syntax OperationName ::= Token{[a-z][a-zA-Z0-9\_]*}            [notInRules]
  syntax PredicateName ::= Token{[a-z][a-zA-Z0-9\_]*}            [notInRules]

  rule P. => P :- .Predicates .                                  [macro]

  rule (On:OperationName => On(.Terms)) , _                      [macro]
  rule (Pn:PredicateName => Pn(.Terms)) :- _ .                   [macro]
  rule (Pn:PredicateName => Pn(.Terms)) , _                      [macro]

  rule [T:Term,Ts:Terms|T':Term] => [T|[Ts|T']] when Ts =/=K .Terms   [macro]
  rule [Ts:Terms] => [Ts|[.Terms]] when Ts =/=K .Terms           [macro]

// dirty trick to avoid semantic conflics with predicates (which are not strict)
// the next term construct is not meant to be used in programs, although it can.
  syntax Predicate ::= PredicateName "of" Terms
  rule Pn:PredicateName(Ts:Terms) => Pn of Ts                    [macro]

endmodule


module LOGIK
  imports LOGIK-SYNTAX
  imports UNIFICATION

// HW: You should complete this module

endmodule
