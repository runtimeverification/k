load ../lib/ml-prelude.maude
load kernelC-syntax
load kernelC-semantics

kmod KERNELC is
  including KERNELC-SEMANTICS
    + MATHEMATICAL-DOMAIN-BUILTIN-MODULE
    + LIST-HP
    + BINARY-TREE-HP

  kvar N M : Nat

  syntax BagItem ::= check ( KLabel )

  macro check(Kl:KLabel) = <T_>
                             <program> Kl(.List{K}) ~> checkContracts </program>
                             <tasks> .Bag </tasks>
                           <_/T>

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

