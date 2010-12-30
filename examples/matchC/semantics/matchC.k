load matchC-syntax
load kernelC-semantics
load matchC-semantics


kmod MATCHC is
  including MATCHC-SEMANTICS
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
                                 <program>
                                   Kl(.List{K}) ~> checkContracts
                                 </program>
                               <_/task>
                             </tasks>
                           <_/top>


***(
Output
***)
  rule
    <feasible> N => N +Int 1 </feasible>
    (
      <task_>
        <k> .K </k>
      <_/task>
    =>
      .Bag
    )
  [metadata "structural"]
  rule
    <infeasible> N => N +Int 1 </infeasible>
    (
      <task_>
        <form> FalseFormula </form>
      <_/task>
    =>
      .Bag
    )
  [metadata "structural"]
endkm

