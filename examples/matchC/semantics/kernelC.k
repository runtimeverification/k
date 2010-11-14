load ../lib/ml-prelude.maude
load kernelC-syntax
load kernelC-semantics

kmod KERNELC is including KERNELC-SEMANTICS
  syntax BagItem ::= run ( KLabel )

  macro run(Kl:KLabel) = <T_>
                           <program> Kl(.List{K}) ~> runMain </program>
                           <tasks> .Bag </tasks>
                         <_/T>
endkm

