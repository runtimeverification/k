---load ../lib/ml-prelude.maude
load matchC-syntax
load matchC-semantics
load kernelC

kmod MATCHC is
  including MATCHC-SEMANTICS
    + KERNELC
    + MATHEMATICAL-DOMAIN-BUILTIN-MODULE
    + LIST-HP
    + BINARY-TREE-HP

  kvar N M : Nat

  syntax BagItem ::= check ( KLabel )
                   | ( Nat feasible and Nat infeasible paths)
                     [format(g! d d d d d o)]

  macro check(Kl:KLabel) = <top_>
                             <check> SetItem(checkContract(main)) </check>
                             <tasks>
                               <task_>
                                 <config_>
                                   <program>
                                     Kl(.List{K}) ~> checkContracts
                                   </program>
                                 <_/config>
                               <_/task>
                             </tasks>
                           <_/top>


***(
Output
***)
  rule
    <feasible> N => N +Int 1 </feasible>
    (
      <config_>
        <k> .K </k>
      <_/config>
    =>
      .Bag
    )
  [metadata "structural"]
  rule
    <infeasible> N => N +Int 1 </infeasible>
    (
      <config_>
        <form> FalseFormula </form>
      <_/config>
    =>
      .Bag
    )
  [metadata "structural"]
endkm

