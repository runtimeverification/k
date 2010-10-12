load imp-semantics
load examples/append.k


kmod IMP is including IMP-SEMANTICS
including TEST

  op check : KLabel -> BagItem
  op (_feasible and_infeasible paths) : Nat Nat -> BagItem
  [format(g! d d d d d o)]

  kvar N M : Nat

  eq check(K:KLabel) = <T>
                         <feasible> 0 </feasible>
                         <infeasible> 0 </infeasible>
                         <spec> mkSpec(K(.List{K})) </spec>
                         <config>
                           <k> K(.List{K}) </k>
                           <env> .Map </env>
                           <struct> .Map </struct>
                           <heap> .Map </heap>
                           <form> TrueFormula </form>
                           <subst> .Subst </subst>
                           <newSym>  1 </newSym>
                           <newImpl> 0 </newImpl>
                         </config>
                       </T>


rule <T> <feasible> N </feasible> <infeasible> M </infeasible> <spec> Mp:Map </spec> </T>
    =>
<T> <feasible> N </feasible> <infeasible> M </infeasible> </T>




  rule
    <T>
      <feasible> N </feasible>
      <infeasible> M </infeasible>
    </T>
    =>
    N feasible and M infeasible paths
  [metadata "structural"]
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

