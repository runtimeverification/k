load ../lib/ml-prelude.maude
load kernelC-syntax
load kernelC-semantics


kmod KERNELC is including KERNELC-SEMANTICS
  syntax BagItem ::= run ( K )

  macro run(K:K) = <config_>
                           <program> K ~> runMain </program>
                         <_/config>
endkm

