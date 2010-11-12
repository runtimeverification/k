load kernelC-semantics

kmod MATCHC-SEMANTICS is including MATCHC-SYNTAX + KERNELC-SEMANTICS
  kvar N : Nat
  kvar I : Int++
  kvar Phi Phi1 Phi2 : Formula
  kvar NtPhi : NtFormula
  kvar Subst Subst1 Subst2 : Subst
  kvar F : Id
  kvar E E1 E2 : Expression
  kvar T : ExpressionType
  kvar S : Statement
  kvar K : K
  kvar ParamList : List{KernelC}
  kvar Cfgs CfgItems PreCfgs PostCfgs : Bag
  kvar Map Env TEnv : Map
  kvar Stack : List

  syntax K ::= checkContracts
  syntax K ::= checkContract ( Id )
  syntax K ::= co-skolemize ( K )
  syntax MapItem ::= ExpressionType Id ( List{KernelC} ) : Bag => Bag

  configuration <T> 
                  <feasible> 0 </feasible>
                  <infeasible> 0 </infeasible>

                  <program> .K </program>
                  <spec> .Map </spec>
                  <struct> .Map </struct>
                  <fun> .Map </fun>

                  <tasks>
                    <config*>
                      <k> .K </k>
                      <stack> .List </stack>
                      <tenv> .Map </tenv>
                      <env> .Map </env>
                      <heap> .Map </heap>
                      <form> TrueFormula </form>
                      <subst> .Subst </subst>
                    </config*>
                  </tasks>

                  <counter> 0 </counter>
                </T>


***(
Function entry
***)
  rule
    <program> checkContracts => .K <_/program>
    <tasks> .Bag </tasks>
  [structural]
  rule
    <program> checkContracts <_/program>
    <fun_> T F(ParamList) /*@ pre PreCfgs */ /*@ post PostCfgs */ |-> S <_/fun>
    <tasks_>
        BagItem(checkContract(F))
      =>
        <config_>
          <k> declParams(ParamList) ~> /*@ assume PreCfgs */ ~> S </k>
          <stack> callContext(/*@ assert PostCfgs */, .Map, .Map) </stack>
        <_/config>
    <_/tasks>
  [structural]
  rule
    <program> checkContracts <_/program>
    <fun_> T F(ParamList) |-> S <_/fun>
    <tasks_>
        BagItem(checkContract(F))
      =>
        <config_>
          <k> declParams(ParamList) ~> S </k>
          <stack> callContext(.K, .Map, .Map) </stack>
        <_/config>
    <_/tasks>
  [structural]


***(
Function definition/declaration
***)
  rule
    <program>
      T F(ParamList) /*@ pre PreCfgs */ /*@ post PostCfgs */ => .K
    <_/program>
    <spec_>
        .Map
      =>
        T F(ParamList)
        |-> (co-skolemize((/*@ assert PreCfgs */ ~> /*@ assume PostCfgs */))
             ~> return getReturnValue(T))
    <_/spec>
  [structural]
  rule
    <program>
      T F(ParamList) /*@ pre PreCfgs */ /*@ post PostCfgs */ S => .K
    <_/program>
    <spec_>
        .Map
      =>
        T F(ParamList)
        |-> (co-skolemize((/*@ assert PreCfgs */ ~> /*@ assume PostCfgs */))
             ~> return getReturnValue(T))
    <_/spec>
    <fun_>
        .Map
      =>
        T F(ParamList) /*@ pre PreCfgs */ /*@ post PostCfgs */
        |-> (S ~> return tv(void, unit))
    <_/fun>
    <tasks_> .Bag => BagItem(checkContract(F)) <_/tasks>
  [structural]
  rule
    <program> (/*@ verify */ => .K) ~> T F(ParamList) S <_/program>
    <tasks_> .Bag => BagItem(checkContract(F)) <_/tasks>
  [structural]
  rule
    <k>
        co-skolemize((/*@ assert PreCfgs */ ~> /*@ assume PostCfgs */))
      =>
        /*@ assert co-skolemize(N, PreCfgs) */
        ~> /*@ assume co-skolemize(N, PostCfgs) */
    <_/k>
    <counter> N => sNat N </counter>
  [structural]


***(
Statements
***)
  rule if (tv(_, I) => tv(int, I) ? tv(int, 1) : tv(int, 0)) _ else _
  if notBool isInt(I) [structural]


***(
Expressions
***)
  rule
    <config>
      <k> (tv(_, I) ? E1 : E2) ~> K </k>
      <form> Phi </form>
      CfgItems
    </config>
  =>
    <config>
      <k> E1 ~> K </k>
      <form> Phi /\ ~(I === 0) </form>
      CfgItems
    </config>
    <config >
      <k > E2 ~> K </k>
      <form> Phi /\ I === 0 </form>
      CfgItems
    </config>
  if notBool isInt(I) [structural]


***(
Memory rearrangement
***)
***(
  rule
    <k> derive(I) <_/k>
    <form> NtPhi => FalseFormula </form>
  if check-sat(NtPhi) ==Bool "unsat"
***)


--------------------------------------------------------------------------------
--- Matching logic annotations                                               ---
--------------------------------------------------------------------------------
***(
loop invariants
  1. must be proven on every path to the loop header, that is, before entering 
     the loop for the first time, and after executing the loop body before
     jumping back at the condition
  2. may be assumed correct after checking the loop condition
***)
  rule
    <k>
        /*@ invariant Cfgs */ ~> while (E) S ~> K
      =>
        /*@ assert Cfgs */ ~> 'if`(_`)_else_(E,, (S ~> /*@ assert Cfgs */),, K)
    </k>

***(
assumed patterns are merged with the current configuration
multiple patterns generate splitting
***) 
  rule
    <config_> 
      <k>
          /*@ assume
            <config>
              <form> Phi2 </form>
              CfgItems
            </config>
            Cfgs
          */
          ~> K
        =>
          /*@ assume Cfgs */ ~> K
      </k>
      <stack> Stack </stack>
      <tenv> TEnv </tenv>
      <form> Phi1 </form>
      <subst> Subst </subst>
    <_/config>
    (
      .Bag
    =>
      <config>
        <k> K </k>
        <stack> Stack </stack>
        <tenv> TEnv </tenv>
        skolemize(N, applySubst(<form> Phi1 /\ Phi2 </form> CfgItems, Subst))
        skolemize(N, <subst> Subst </subst>)
      </config>
    )
    <counter> N </counter>
  rule
    (
      <config_>
        <k> /*@ assume .Bag */ <_/k>
      <_/config>
    =>
      .Bag
    )
    <counter> N => sNat N </counter>

***(
asserted patterns
  1. must be matched the current configuration, that is, the implication
     current configuration ===> asserted patterns can rewrite to true (the rule
     searches for the existance of a proof in the side condition, and also
     returns facts found out to be true during the search for a proof)
  2. may be assumed correct afterward
***)
  rule
    <config>
      <k> /*@ assert Cfgs */ => /*@ assume Cfgs */ <_/k>
      <stack> Stack </stack>
      <tenv> TEnv </tenv>
      <subst> Subst1 => Subst2 </subst>
      CfgItems
    </config>
    <counter> N </counter>
  if search(
      <config>
        <subst> Subst1 </subst>
        CfgItems
      </config>
      ===>
      Cfgs
    =>
      <config>
        <form> TrueFormula </form>
        <subst> Subst2 </subst>
      </config>
    )
endkm

