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

***(
  --- does not work, weird error message
  syntax Bag ::= Bag /\ Formula
               | Formula /\ Bag

  kvar Cfg : BagItem
  kvar Cfgs CfgItems : Bag
  kvar Phi : Formula

  rule Phi /\ Cfgs => Cfgs /\ Phi [structural]
  rule (Cfg Cfgs) /\ Phi => (Cfg /\ Phi) (Cfgs /\ Phi) [structural]
  rule
      <config> CfgItems </config> /\ Phi
    => 
      <config> CfgItems <form> Phi </form> </config>
  [structural]
***)
endkm

