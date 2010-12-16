load ../lib/ml-prelude.maude
load kernelC-syntax
load kernelC-semantics


kmod KERNELC is including KERNELC-SEMANTICS
  syntax BagItem ::= run ( KLabel )

  macro run(Kl:KLabel) = <config_>
                           <program> Kl(.List{K}) ~> runMain </program>
                         <_/config>
endkm

