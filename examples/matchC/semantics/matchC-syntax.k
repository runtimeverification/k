load kernelC-syntax

kmod MATCHC-SYNTAX is including KERNELC-SYNTAX
***(
matching logic annotations
***)
  syntax Annotation ::= /*@`assume Bag */ ---[strat(0)]
                      | /*@`assert Bag */ ---[strat(0)]
                      | /*@`invariant Bag */ ---[strat(0)]

  syntax Annotation ::= /*@`pre Bag */ ---[strat(0)]
                      | /*@`post Bag */ ---[strat(0)]

  syntax Annotation ::= /*@`verify`*/


  syntax FunctionDeclaration ::= ExpressionType
                                   Id
                                   ( List{KernelC} )
                                   Annotation
                                   Annotation
  syntax FunctionDefinition ::= ExpressionType
                                  Id
                                  ( List{KernelC} )
                                  Annotation
                                  Annotation
                                  Statement
  syntax Declaration ::= Annotation
  syntax Statement ::= Annotation
endkm

