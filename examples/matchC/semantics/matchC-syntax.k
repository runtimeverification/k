load kernelC-syntax


kmod MATCHC-SYNTAX is including KERNELC-SYNTAX
***(
matching logic annotations
***)
  syntax List ::= Pattern

  syntax Annotation ::= @`assume List 
                      | @`assert List 
                      | @`inv List 

  syntax Annotation ::= @`cfg Bag -> Bag req Formula ens Formula
                      | @`cfg Bag -> Bag if Formula

  syntax Annotation ::= @`verify
                      | @`skip
                      | @`breakpoint
***(
  syntax Annotation ::= @`assume Pattern 
                      | @`assert Pattern 
                      | @`inv Pattern 

  syntax Annotation ::= @`pre Pattern 
                      | @`post Pattern 

  syntax Annotation ::= @`verify`
                      | @`skip`
                      | @`breakpoint
***)

  syntax FunctionDeclaration ::= ExpressionType
                                   Id
                                   ( List{KernelC} )
                                   [[ Annotation ]]
  syntax FunctionDefinition ::= ExpressionType
                                  Id
                                  ( List{KernelC} )
                                  [[ Annotation ]]
                                  Statement
  syntax Declaration ::= Annotation
  syntax Statement ::= Annotation

  syntax Statement ::= returnAssert Expression [strict]
  syntax Expression ::= getReturnValue ( ExpressionType )

  syntax K ::= defaultKItem ( String ) 
             | cleanFrameSubst ( String ) 
             | cleanCallSubst ( Nat ) 
endkm

