load imp-semantics
load parser/list-reverse.maude


kmod IMP is including IMP-SEMANTICS + P-LIST-REVERSE

  op check : KLabel -> BagItem
  op (_feasible and_infeasible paths) : Nat Nat -> BagItem
  [format(g! d d d d d o)]

  kvar N M : Nat

  eq check(Kl:KLabel) = <T>
                          <feasible> 0 </feasible>
                          <infeasible> 0 </infeasible>
                          <spec> .Map </spec>
                          <struct> .Map </struct>
                          <fun> .Map </fun>
                          <counter> 0 </counter>
                          <config>
                            <k> Kl(.List{K}) </k>
                            <tenv> .Map </tenv>
                            <env> .Map </env>
                            <heap> .Map </heap>
                            <form> TrueFormula </form>
                            <subst> .Subst </subst>
                          </config>
                        </T>


  rule
    <T>
      <feasible> N </feasible>
      <infeasible> M </infeasible>
      (
        <spec> _:Map </spec>
        <struct> _:Map </struct>
        <fun> _:Map </fun>
        <counter> _:Nat </counter>
      =>
        .Bag
      )
    </T>
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

