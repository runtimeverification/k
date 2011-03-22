kmod KERNELC-SYNTAX is including ML-K + PL-STRING
***(
imp type system
***)
  syntax Void ::= void
  syntax NvExpressionType ::= int
                            | string
                            | struct Id [prec 10]
                            | ExpressionType *
  syntax ExpressionType ::= Void | NvExpressionType


***(
declarations, function definitions and top level constructs
***)
  syntax Declaration ::= FunctionDeclaration
                       | StructDeclaration
                       | VariableDeclaration
  syntax VariableDeclaration ::= ExpressionType Id ;
  syntax StructDeclaration ::= struct Id { List{KernelC} } ;
  syntax FunctionDeclaration ::= ExpressionType
                                   Id
                                   ( List{KernelC} )
  syntax FunctionDefinition ::= ExpressionType
                                  Id
                                  ( List{KernelC} )
                                  Statement

  syntax TranslationUnit ::= translationUnit KernelC


***(
imp statements
***)
  syntax Statement ::= nop
                     | Expression ; [strict]
                     | block ( KernelC )
                     | if ( Expression ) Statement else Statement [strict(1)]
                     | while ( Expression ) Statement
                     | return Expression [strict]
                     | ExtraStatement
  syntax ExtraStatement ::= breakpoint
                          | watch


***(
imp Expressions
***)
  syntax Expression ::= TypedValue
                      | Id
                      | String 
*** unary Expressions
                      | - Expression [strict]
                      ---| + Expression [strict]
                      | `! Expression [strict]
                      | * Expression [strict]
                      | & Expression
                      ---| ++ Expression [strict]
                      ---| -- Expression [strict]
                      ---| Expression ++ [strict]
                      ---| Expression -- [strict]
*** binary Expressions
                      | Expression + Expression [strict]
                      | Expression - Expression [strict]
                      | Expression * Expression [strict]
                      | Expression / Expression [strict]
                      | Expression % Expression [strict]
                      | Expression << Expression [strict]
                      | Expression >> Expression [strict]
                      | Expression < Expression [strict]
                      | Expression <= Expression [strict]
                      | Expression > Expression [strict]
                      | Expression >= Expression [strict]
                      | Expression == Expression [strict] 
                      | Expression != Expression
                      ---| Expression & Expression [strict] 
                      ---| Expression ^ Expression [strict] 
                      ---| Expression `| Expression [strict] 
                      | Expression && Expression [strict(1)]
                      | Expression || Expression [strict(1)]
                      | Expression = Expression [strict(2)]
                      | Expression *= Expression
                      | Expression /= Expression
                      | Expression %= Expression
                      | Expression += Expression
                      | Expression -= Expression
                      | Expression <<= Expression
                      | Expression >>= Expression
                      ---| Expression &= Expression
                      ---| Expression ^= Expression
                      ---| Expression |= Expression
*** conditional expression
                      | Expression `? Expression : Expression [strict(1)]
*** cast
                      | ( ExpressionType ) Expression [strict(2)]
*** function calls
                      | Expression ( List{KernelC} ) [strict(2)]
*** sizeof
                      | sizeof Expression
                      | sizeof ExpressionType
*** array indexing
                      | Expression `[ Expression `]
*** members of structures
                      | Expression -> Id [strict(1)]
*** memory management
                      | new ExpressionType
                      | delete Expression [strict]
*** extra stuff, not part of the language syntax, but helpful for the semantics
                      | ExpressionHelper
  syntax ExpressionHelper ::= load ( ExpressionType , Value )
                            | store ( ExpressionType , Value , Value )
                            | read ( ExpressionType )
                            | offset ( ExpressionType , Id )
                            | new ExpressionType
                            | detele TypedValue
                            | deleteObject ( Value , Nat )


***(
KernelC is a top sort
***)
  syntax KernelC ::= TranslationUnit
                   | FunctionDefinition
                   | Declaration
                   | arg ExpressionType Expression
                   | ExpressionType
                   | Statement
                   | Expression

*** arrow
  syntax KernelC ::= .KernelC
                   | KernelC ~~> KernelC

*** list
  syntax List{KernelC} ::= .List{KernelC}
                         | KernelC
                         | List{KernelC} ,,, List{KernelC}
                           [assoc id: .List{KernelC} hybrid strict]
endkm


kmod KERNELC-DESUGARED-SYNTAX is including KERNELC-SYNTAX
--------------------------------------------------------------------------------
--- This module desugars some KERNELC language constructs into core ones.    ---
--- The idea is that we only want to give semantics to core constructs,      ---
--- so we get rid of the derived ones before we start the semantics.         ---
--------------------------------------------------------------------------------
  ---macro NULL = 0
  rule nop => .K [structural]
  rule .KernelC => .K [structural]
  rule KC1:KernelC ~~> KC2:KernelC => KC1:KernelC ~> KC2:KernelC [structural]
endkm

