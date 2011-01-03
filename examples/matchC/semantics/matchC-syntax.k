load kernelC-syntax


kmod MATCHC-SYNTAX is including KERNELC-SYNTAX
***(
matching logic annotations
***)
  syntax List ::= Pattern
  syntax Annotation ::= /*@`assume List */
                      | /*@`assert List */
                      | /*@`invariant List */

  syntax Annotation ::= /*@`pre List */
                      | /*@`post List */

  syntax Annotation ::= /*@`verify`*/
                      | /*@`skip`*/
***(
  syntax Annotation ::= /*@`assume Pattern */
                      | /*@`assert Pattern */
                      | /*@`invariant Pattern */

  syntax Annotation ::= /*@`pre Pattern */
                      | /*@`post Pattern */

  syntax Annotation ::= /*@`verify`*/
                      | /*@`skip`*/
***)


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

  syntax K ::= defaultKItem ( String )
  syntax K ::= String
endkm

