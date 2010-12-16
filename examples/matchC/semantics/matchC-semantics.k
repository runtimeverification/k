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
  kvar checkSet Set : Set


  syntax K ::= checkContracts
             | checkContract ( Id )
             | uncheckContract ( Id )
  syntax K ::= co-skolemize ( K )


  configuration <top> 
                  <feasible> 0 </feasible>
                  <infeasible> 0 </infeasible>

                  <check> .Set </check>

                  <tasks>
                    <task*>
                      <config> 
                        <program> .K </program>
                        <struct> .Map </struct>
                        <fun> .Map </fun>
      
                        <k> .K </k>
                        <env> .Map </env>
                        <stack> .List </stack>
                        <tenv> .Map </tenv>
                        
                        <heap> .Map </heap>
      
                        <in> .List </in>
                        <out> .List </out>
      
                        <counter> 0 </counter>
                      </config>

                      <form> TrueFormula </form>
                      <subst> .Subst </subst>
                    </task*>
                  </tasks>

                  <other-counter> 0 </other-counter>
                </top>


  rule
    <program> checkContracts => setToK(checkSet) <_/program>
    <check> checkSet </check>
  [structural]
  rule
    <check_>
      SetItem(checkContract(F)) SetItem(uncheckContract(F)) => .Set
    <_/check>
  [structural]


***(
Function entry
***)
  rule
    <program> checkContract(F) => .K <_/program>
    <fun_> T F(ParamList) /*@ pre PreCfgs */ /*@ post PostCfgs */ |-> S <_/fun>
    <tasks_>
        .Bag
      =>
        <config_>
          <k> declParams(ParamList) ~> /*@ assume PreCfgs */ ~> S </k>
          <stack> callContext(/*@ assert PostCfgs */, .Map, .Map) </stack>
        <_/config>
    <_/tasks>
  [structural]
  rule
    <program> checkContract(F) => .K <_/program>
    <fun_> T F(ParamList) |-> S <_/fun>
    <tasks_>
        .Bag
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
    <fun_>
        .Map
      =>
        T F(ParamList) /*@ pre PreCfgs */ /*@ post PostCfgs */ |-> .K
    <_/fun>
  [structural]
  rule
    <program>
      T F(ParamList) /*@ pre PreCfgs */ /*@ post PostCfgs */ S => .K
    <_/program>
    <fun_>
        .Map
      =>
        T F(ParamList) /*@ pre PreCfgs */ /*@ post PostCfgs */
        |-> (S ~> return tv(void, unit))
    <_/fun>
    <check_> .Set => SetItem(checkContract(F)) <_/check>
  [structural]
  rule
    <program> (/*@ verify */ => .K) ~> T F(ParamList) S <_/program>
    <check_> .Set => SetItem(checkContract(F)) <_/check>
  [structural]
  rule
    <program> (/*@ skip */ => .K) ~> T F(ParamList) S <_/program>
    <check_> .Set => SetItem(uncheckContract(F)) <_/check>


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
summary function calls
***)
  rule
    <fun_>
      T F(ParamList) /*@ pre PreCfgs */ /*@ post PostCfgs */ |-> _
    <_/fun>
    <k>
        _`(_`)(F, ArgList) ~> K
      =>
        declParams(ParamList)
        ~> bindParams(ParamList, ArgList)
        ~> /*@ assert co-skolemize(N, PreCfgs) */
        ~> /*@ assume co-skolemize(N, PostCfgs) */
        ~> return getReturnValue(T)

    </k>
    <stack_> .List => callContext(getReturnValue(T) ~> K, TEnv, Env) </stack>
    <tenv> TEnv => .Map </tenv>
    <env> Env => .Map </env>
    <other-counter> N => sNat N </other-counter>
  [structural]


***(
Memory rearrangement
***)
***(
  rule
    <k> derive(I) <_/k>
    <form> NtPhi => FalseFormula </form>
  if check-sat(NtPhi) ==Bool "unsat"
***)
  rule
    <heap_> N |-> _:_ <_/heap>
    <form> _ => FalseFormula </form>


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
assumed patterns
  1. are merged with the current configuration
  2. split the current configuration if the contain disjunctions
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
    <other-counter> N </other-counter>
  rule
    (
      <config_>
        <k> /*@ assume .Bag */ <_/k>
      <_/config>
    =>
      .Bag
    )
    <other-counter> N => sNat N </other-counter>

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
    <other-counter> N </other-counter>
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


***(
Helpers
***)
  syntax K ::= setToK ( Set )
  rule setToK(SetItem(K) Set) => K ~> setToK(Set) [structural]
  rule setToK(.Set) => .K [structural]
endkm

