load kernelC-syntax

kmod MATCHC-SYNTAX is including KERNELC-SYNTAX
***(
matching logic annotations
***)
  syntax Annotation ::= /*@`assume Bag */
                      | /*@`assert Bag */
                      | /*@`invariant Bag */

  syntax Annotation ::= /*@`pre Bag */
                      | /*@`post Bag */

  syntax Annotation ::= /*@`verify`*/
                      | /*@`skip`*/


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

