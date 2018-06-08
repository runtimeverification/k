require "symbolic.k"

module LOGIK-COMMON
  imports DOMAINS-SYNTAX

  syntax OperationName
  syntax Term ::= Int
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

  syntax Val ::= OperationName "(" Vals ")"
  syntax Vals ::= List{Val,","}

  syntax PredicateName
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

  rule [T1:Term,T2:Term,Ts:Terms|T':Term] => [T1|[T2,Ts|T']]      [macro]
  rule [T:Term,Ts:Terms] => [T,Ts|[.Terms]]                      [macro]

endmodule

module LOGIK-SYNTAX
  imports LOGIK-COMMON
  imports BUILTIN-ID-TOKENS

  syntax #KVariable ::= r"[A-Z_][A-Za-z0-9_]*"   [token, prec(2), autoReject]
                      | #UpperId                 [token, autoReject]
  syntax Term ::= #KVariable [klabel(#SemanticCastToTerm)]
  syntax OperationName ::= r"[a-z][a-zA-Z0-9_]*"                 [autoReject, token]
                         | #LowerId                              [autoReject, token]
  syntax PredicateName ::= r"[a-z][a-zA-Z0-9_]*"                 [autoReject, token]
                         | #LowerId                              [autoReject, token]

endmodule


module LOGIK
  imports LOGIK-COMMON
  imports DOMAINS
  imports UNIFICATION

// HW: You should complete this module

endmodule
