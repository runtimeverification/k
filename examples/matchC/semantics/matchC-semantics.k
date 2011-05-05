load kernelC-semantics


kmod MATCHC-SEMANTICS is including MATCHC-SYNTAX + KERNELC-SEMANTICS
  kvar N Counter : Nat
  kvar I : Int++
  kvar VarRoot : String
  kvar Phi PrePhi PostPhi Phi1 Phi2 : Formula
  kvar NtPhi : NtFormula
  kvar Subst Subst1 Subst2 : Subst
  kvar V : Value
  kvar F X FName : Id
  kvar E E1 E2 : Expression
  kvar T : ExpressionType
  kvar NvT : NvExpressionType
  kvar S : Statement
  kvar K Program : K
  kvar ParamList ArgList : List{KernelC}
  kvar Annot : Annotation 
  kvar PreCfg PostCfg CfgItems CfgItems1 CfgItems2 TaskItems : Bag 
  kvar Pattern Pattern1 Pattern2 : Pattern
  kvar Env TEnv StructMap FunMap : Map
  kvar Stack : List
  kvar checkSet Set : Set


  syntax K ::= checkContracts
             | checkContract ( Id )
             | uncheckContract ( Id )

***(
  syntax K ::= assumeNormal ( Pattern )
            |  assertNormal ( Pattern )
***)
  syntax K ::= assumeNormal ( List )
            |  assertNormal ( List )

  syntax K ::= assertLabel

  syntax K ::= disolveTask

  syntax K ::= `Run
             | `Hypothesis
             | `Conclusion
             | `Constrain

  configuration <top> 
                  <feasible> -1 </feasible>
                  <infeasible> 0 </infeasible>

                  <check> .Set </check>

                  <mainOut> .List </mainOut>

                  <tasks>
                    <funTask multiplicity="*">
                      <funId> .K </funId>
                      <task multiplicity="*">
                        <taskType> Run </taskType>

                        <config> 
                          <program> .K </program>
                          <struct> .Map </struct>
                          <fun> .Map </fun>

                          <k> .K </k>
                          <env> .Map </env>
                          <stack> .List </stack>
                          <fname> .K </fname>
                          <tenv> .Map </tenv>

                          <heap> .Map </heap>

                          <in> .List </in>
                          <out> .List </out>

                          <counter> 0 </counter>
                        </config>

                        <form> TrueFormula </form>
                        <subst> .Subst </subst>
                      </task>
                    </funTask>
                  </tasks>
                </top>


  rule
    <program> checkContracts => setToK(checkSet) <_/program>
    <check> checkSet </check>
  [structural print "\\{print tr\\}DONE!\n\\{print o\\}Verifying program ..."]
  rule
    <check_>
      SetItem(checkContract(F)) SetItem(uncheckContract(F)) => .Set
    <_/check>
  [structural]


***(
Function entry
***)
  rule
    <funTask_>
      <task_>
        <program> checkContract(F) => .K <_/program>
        <struct> StructMap </struct>
        <fun>
          T F(ParamList) [[@ cfg PreCfg -> PostCfg req PrePhi ens PostPhi]]
            |-> S
          FunMap
        </fun>
      <_/task>
    <_/funTask>
    (
      .Bag
    =>
      <funTask_>
        <funId> F </funId>
        <task_>
          <struct> StructMap </struct>
          <fun>
            T F(ParamList) [[@ cfg PreCfg -> PostCfg req PrePhi ens PostPhi]]
              |-> S
            FunMap
          </fun>
          <k>
            declParams(ParamList)
            ~> @ assume (PreCfg /\ PrePhi)
            ~> substKLabel(S, 'return_, 'returnAssert_)
            ~> assertLabel
            ~> @ assert (PostCfg /\ PostPhi)
            ~> disolveTask
          </k>
          <fname> F </fname>
        <_/task>
      <_/funTask>
    )
  [structural]
  rule
    <funTask_>
      <task_>
        <program> checkContract(F) => .K <_/program>
        <struct> StructMap </struct>
        <fun> T F(ParamList) |-> S FunMap </fun>
      <_/task>
    <_/funTask>
    (
      .Bag
    =>
      <funTask_>
        <funId> F </funId>
        <task_>
          <struct> StructMap </struct>
          <fun> T F(ParamList) |-> S FunMap </fun>
          <k>
            declParams(ParamList)
            ~> substKLabel(S, 'return_, 'returnAssert_)
            ~> assertLabel
          </k>
          <fname> F </fname>
        <_/task>
      <_/funTask>
    )
  [structural]


***(
Function definition/declaration
***)
  rule
    <program>
        T F(ParamList) [[@ cfg PreCfg -> PostCfg if Phi]]
      =>
        T F(ParamList) [[@ cfg PreCfg -> PostCfg req filterPrePhi(Phi) ens Phi]]
    <_/program>
  [structural]
  rule
    <program>
        T F(ParamList) [[@ cfg PreCfg -> PostCfg if Phi]] S
      =>
        T F(ParamList)
        [[@ cfg PreCfg -> PostCfg req filterPrePhi(Phi) ens Phi]]
        S
    <_/program>
  [structural]
  rule
    <program>
      T F(ParamList) [[@ cfg PreCfg -> PostCfg req PrePhi ens PostPhi]] => .K
    <_/program>
    <fun_>
        .Map
      =>
        T F(ParamList)
        [[@ cfg applyDefaultSubst(
                  PreCfg,
                  defaultMapItem("env") <- defaultFreeEnv(paramSet(ParamList))
                )
            ->
                applyDefaultSubst(
                  PostCfg,
                  defaultMapItem("env") <- defaultEnv(paramSet(ParamList))
                )
            req PrePhi ens PostPhi]]
        |-> .K
    <_/fun>
  [structural]
  rule
    <program>
      T F(ParamList) [[@ cfg PreCfg -> PostCfg req PrePhi ens PostPhi]] S => .K
    <_/program>
    <fun_>
        .Map
      =>
        T F(ParamList)
        [[@ cfg applyDefaultSubst(
                  PreCfg,
                  defaultMapItem("env") <- defaultFreeEnv(paramSet(ParamList))
                )
            ->
                PostCfg
                //applyDefaultSubst(
                //  PostCfg,
                //  defaultMapItem("env") <- defaultEnv(paramSet(ParamList))
                //)
            req PrePhi ens PostPhi]]
        |-> (S ~> return tv(void, unit))
    <_/fun>
    <check_> .Set => SetItem(checkContract(F)) <_/check>
  [structural]
***(
  rule
    <program> T F(ParamList) [[Annot]] S => .K <_/program>
    <fun_>
      .Map => T F(ParamList) [[Annot]] |-> (S ~> return tv(void, unit))
    <_/fun>
    <check_> .Set => SetItem(checkContract(F)) <_/check>
  [structural]
***)
  rule
    <program> (@ verify  => .K) ~> T F(ParamList) S <_/program>
    <check_> .Set => SetItem(checkContract(F)) <_/check>
  [structural]
  rule
    <program> (@ skip  => .K) ~> T F(ParamList) S <_/program>
    <check_> .Set => SetItem(uncheckContract(F)) <_/check>


***(
Return & Assert
***)
  rule
    <k> returnAssert tv(_, V) ~> _ ~> assertLabel => .K <_/k>
    ---<form> Phi => returns V /\ Phi </form>
    <env_> .Map => id("__return__") |-> V <_/form>


***(
Statements
***)
  rule if (tv(_, I) => tv(int, I) ? tv(int, 1) : tv(int, 0)) _ else _
  if notBool isInt(I) [structural]


***(
Expressions
***)
  rule
    <task>
      <config>
        <k> (tv(_, I) ? E1 : E2) ~> K </k>
        CfgItems
      </config>
      <form> Phi </form>
      TaskItems
    </task>
  =>
    <task>
      <config>
        <k> E1 ~> K </k>
        CfgItems
      </config>
      <form> Phi /\ ~(I === 0) </form>
      TaskItems
    </task>
    <task>
      <config >
        <k > E2 ~> K </k>
        CfgItems
      </config>
      <form> Phi /\ I === 0 </form>
      TaskItems
    </task>
  if notBool isInt(I)


***(
summary function calls
***)
  rule
    <fun_>
      T F(ParamList) [[@ cfg PreCfg -> PostCfg req PrePhi ens PostPhi]] |-> _
    <_/fun>
    <k>
        _`(_`)(F, ArgList) ~> K
      =>
        declParams(ParamList)
        ~> bindParams(ParamList, ArgList)
        ~> @ assert co-skolemize(N, PreCfg /\ PrePhi)
        ~> @ assume co-skolemize(N, PostCfg /\ PostPhi)
        ~> cleanCallSubst(N)
        ~> return getReturnValue(T)

    </k>
    <stack> .List => callContext(FName, K, TEnv, Env) <_/stack>
    <fname> FName </fname>
    <tenv> TEnv => .Map </tenv>
    <env> Env => .Map </env>
    <counter> N => sNat N </counter>
  [structural]

*** retrieve the return value
  rule
    <k> getReturnValue(NvT) => tv(NvT, V) <_/k>
    <env_> id("__return__") |-> V => .Map <_/env>
  [structural]
  rule <k> getReturnValue(void) => tv(void, unit) <_/k> [structural]


***(
Memory rearrangement
***)
  rule
    <k> derive(I) <_/k>
    <form> NtPhi => FalseFormula </form>
  if check-validity(~ NtPhi)
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
        @ inv Pattern ~> while (E) S ~> K
      =>
        @ assert Pattern
        ~> 'if`(_`)_else_(E,, (S ~> @ assert Pattern ~> disolveTask),, K)
    </k>


***(
assumed patterns
  1. are merged with the current configuration
  2. split the current configuration if they contain disjunctions
***)
  rule
    <funId> F </funId>
    <k>
      (
        @ assume Pattern 
      =>
        assumeNormal(
          skolemize(
            N,
            applySubst(
              applyDefaultSubst(
                Pattern,
                (defaultKItem("program") <- Program) ;;
                (defaultMapItem("struct") <- StructMap) ;;
                (defaultMapItem("fun") <- FunMap) ;;
                ---(defaultKItem("k") <- K) ;;
                (defaultMapItem("FreeEnv") <- defaultFreeEnv(keys(TEnv))) ;;
                (defaultMapItem("env") <- defaultEnv(keys(TEnv))) ;;
                (defaultKItem("fname") <- FName) ;;
                (defaultMapItem("tenv") <- TEnv) ;;
                (defaultKItem("counter") <- sNat N)
              ),
              Subst
            )
          )
        )
      )
      ~> K
    </k>
    <program> Program </program>
    <struct> StructMap </struct>
    <fun> FunMap </fun>
    <env> Env </env>
    <fname> FName </fname>
    <tenv> TEnv </tenv>
    <counter> N => sNat N </counter>
    <subst> Subst </subst>
  [structural]
  rule
    <task>
      <config>
        <k> assumeNormal(Pattern1 \/ Pattern2) ~> K </k>
        CfgItems
      </config>
      TaskItems
    </task>
  =>
    <task>
      <config>
        <k> assumeNormal(Pattern1) ~> K </k>
        CfgItems
      </config>
      TaskItems
    </task>
    <task>
      <config>
        <k> assumeNormal(Pattern2) ~> K </k>
        CfgItems
      </config>
      TaskItems
    </task>
  [structural]
  rule
    <funId> F </funId>
    <task_>
      <config> 
        <k>
          assumeNormal(<config> CfgItems </config> /\ Phi2) => .K
        <_/k>
        (_ => CfgItems)
      </config>
      <form> Phi1 => Phi1 /\ Phi2 </form>
    <_/task>
  [structural]


***(
asserted patterns
  1. must be matched the current configuration, that is, the implication
     current configuration ===> asserted patterns can rewrite to true (the rule
     searches for the existance of a proof in the side condition, and also
     returns facts found out to be true during the search for a proof)
  2. may be assumed correct afterward
***)
  rule
    <funId> F </funId>
    <k>
      (
        @ assert Pattern 
      =>
        assertNormal(
          applySubst(
            applyDefaultSubst(
              Pattern,
              //(defaultKItem("program") <- Program) ;;
              //(defaultMapItem("struct") <- StructMap) ;;
              //(defaultMapItem("fun") <- FunMap) ;;
              //(defaultKItem("k") <- K) ;;
              (defaultMapItem("FreeEnv") <- defaultFreeEnv(keys(TEnv))) ;;
              (defaultMapItem("env") <- defaultEnv(keys(TEnv)))
              //(defaultKItem("fname") <- FName) ;;
              //(defaultMapItem("tenv") <- TEnv) ;;
              //(defaultKItem("counter") <- Counter) 
            ),
            Subst
          )
        )
      )
      ~> K
    </k>
    <program> Program </program>
    <struct> StructMap </struct>
    <fun> FunMap </fun>
    <env> Env </env>
    <fname> FName </fname>
    <tenv> TEnv </tenv>
    <counter> Counter </counter>
    <subst> Subst </subst>
  [structural print ">>>"]
  rule
    <task>
      <taskType> Run </taskType>
      <config>
        <k>
          (
            assertNormal(<config> CfgItems2 </config> /\ Phi)
          =>
            @ assume (<config> CfgItems2 </config> /\ Phi)
          )
          ~> K
        </k>
        CfgItems1
      </config>
      <subst> Subst1 => Subst2 </subst>
      TaskItems
    </task>
  if search(
      <task>
        <taskType> Hypothesis </taskType>
        <config> CfgItems1 </config>
        <subst> .Subst </subst>
        TaskItems
      </task>
      <task>
        <taskType> Conclusion </taskType>
        <config> CfgItems2 </config>
        <form> Phi </form>
        <subst> Subst1 </subst>
      </task>
    =>
      <task>
        <taskType> Constrain </taskType>
        <config> .Bag </config>
        <form> TrueFormula </form>
        <subst> Subst2 </subst>
      </task>
    )


***(
Helpers
***)
  syntax K ::= setToK ( Set )
  rule setToK(SetItem(K) Set) => K ~> setToK(Set) [structural]
  rule setToK(.Set) => .K [structural]

  syntax Set ::= paramSet ( List{KernelC} )
  rule
    paramSet((_ X;),,,ParamList) => SetItem(X) paramSet(ParamList)
  [structural]
  rule paramSet(.List{KernelC}) => .Set [structural]

  syntax Map ::= defaultEnv ( Set )
  rule defaultEnv(SetItem(X) Set) => X |-> ?var(X) defaultEnv(Set) [structural]
  rule defaultEnv(.Set) => .Map [ structural]

  syntax Map ::= defaultFreeEnv ( Set )
  rule
    defaultFreeEnv(SetItem(X) Set) => X |-> FreeVar(X) defaultFreeEnv(Set)
  [structural]
  rule defaultFreeEnv(.Set) => .Map [ structural]

  rule
    <k> cleanFrameSubst(VarRoot) => .K <_/k>
    <subst> Subst => filterFrame!Subst(Subst, VarRoot) </subst>
  [structural]

  rule
    <k> cleanCallSubst(N) => .K <_/k>
    <subst> Subst => filterCallCoSkolemSubst(Subst) </subst>
  [structural]
endkm

