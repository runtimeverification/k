load kernelC-semantics


kmod MATCHC-SEMANTICS is including MATCHC-SYNTAX + KERNELC-SEMANTICS
  kvar N Counter : Nat
  kvar I : Int++
  kvar VarRoot : String
  kvar Phi Phi1 Phi2 : Formula
  kvar NtPhi : NtFormula
  kvar Subst Subst1 Subst2 : Subst
  kvar V : Value
  kvar F X : Id
  kvar E E1 E2 : Expression
  kvar T : ExpressionType
  kvar NvT : NvExpressionType
  kvar S : Statement
  kvar K Program : K
  kvar ParamList ArgList: List{KernelC}
  kvar CfgItems CfgItems1 CfgItems2 TaskItems : Bag 
  kvar Pattern Pattern1 Pattern2 PrePattern PostPattern : Pattern
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

                  <tasks>
                    <task*>
                      <taskType> Run </taskType>
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
    <task_>
      <program> checkContract(F) => .K <_/program>
      <struct> StructMap </struct>
      <fun>
        T F(ParamList) @ pre PrePattern  @ post PostPattern  |-> S
        FunMap
      </fun>
    <_/task>
    (
      .Bag
    =>
      <task_>
        <struct> StructMap </struct>
        <fun>
          T F(ParamList) @ pre PrePattern  @ post PostPattern  |-> S
          FunMap
        </fun>
        <k>
          declParams(ParamList)
          ~> @ assume PrePattern 
          ~> substKLabel(S, 'return_, 'returnAssert_)
          ~> assertLabel
          ~> @ assert PostPattern
          ~> disolveTask
        </k>
      <_/task>
    )
  [structural]
  rule
    <task_>
      <program> checkContract(F) => .K <_/program>
      <struct> StructMap </struct>
      <fun> T F(ParamList) |-> S FunMap </fun>
    <_/task>
    (
      .Bag
    =>
      <task_>
        <struct> StructMap </struct>
        <fun> T F(ParamList) |-> S FunMap </fun>
        <k>
          declParams(ParamList)
          ~> substKLabel(S, 'return_, 'returnAssert_)
          ~> assertLabel
        </k>
      <_/task>
    )
  [structural]


***(
Function definition/declaration
***)
  rule
    <program>
      T F(ParamList) @ pre PrePattern  @ post PostPattern  => .K
    <_/program>
    <fun_>
        .Map
      =>
        T F(ParamList) @ pre PrePattern  @ post PostPattern  |-> .K
    <_/fun>
  [structural]
  rule
    <program>
      T F(ParamList) @ pre PrePattern  @ post PostPattern  S => .K
    <_/program>
    <fun_>
        .Map
      =>
        T F(ParamList) @ pre PrePattern  @ post PostPattern 
        |-> (S ~> return tv(void, unit))
    <_/fun>
    <check_> .Set => SetItem(checkContract(F)) <_/check>
  [structural]
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
    <form> Phi => returns V /\ Phi </form>


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
      T F(ParamList) @ pre PrePattern  @ post PostPattern  |-> _
    <_/fun>
    <k>
        _`(_`)(F, ArgList) ~> K
      =>
        declParams(ParamList)
        ~> bindParams(ParamList, ArgList)
        ~> @ assert co-skolemize(N, PrePattern)
        ~> @ assume co-skolemize(N, PostPattern)
        ~> cleanCallSubst(N)
        ~> return getReturnValue(T)

    </k>
    <stack_> .List => callContext(K, TEnv, Env) </stack>
    <tenv> TEnv => .Map </tenv>
    <env> Env => .Map </env>
    <other-counter> N => sNat N </other-counter>
  [structural]

*** retrieve the return value
  rule
    <k> getReturnValue(NvT) => tv(NvT, V) <_/k>
    <form> Phi /\ returns V => Phi </form>
  [structural]
  rule <k> getReturnValue(void) => tv(void, unit) <_/k> [structural]


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
        @ invariant Pattern 
        ~> while (E) S ~> K
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
                (defaultMapItem("env") <- defaultEnv(Env)) ;;
                (defaultMapItem("tenv") <- TEnv) ;;
                (defaultKItem("counter") <- Counter)
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
    <tenv> TEnv </tenv>
    <counter> Counter </counter>
    <subst> Subst </subst>
    <other-counter> N => sNat N </other-counter>
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
  ---[structural]
  rule
    <task_>
      <config> 
        <k>
          assumeNormal(<config> <k> K </k> CfgItems </config> /\ Phi2) => .K
        <_/k>
        (_ => CfgItems)
      </config>
      <form> Phi1 => Phi1 /\ Phi2 </form>
    <_/task>

***(
asserted patterns
  1. must be matched the current configuration, that is, the implication
     current configuration ===> asserted patterns can rewrite to true (the rule
     searches for the existance of a proof in the side condition, and also
     returns facts found out to be true during the search for a proof)
  2. may be assumed correct afterward
***)
  rule
    <k>
      (
        @ assert Pattern 
      =>
        assertNormal(
          applySubst(
            applyDefaultSubst(
              Pattern,
              (defaultKItem("program") <- Program) ;;
              (defaultMapItem("struct") <- StructMap) ;;
              (defaultMapItem("fun") <- FunMap) ;;
              ---(defaultKItem("k") <- K) ;;
              (defaultMapItem("env") <- defaultEnv(Env)) ;;
              (defaultMapItem("tenv") <- TEnv) ;;
              (defaultKItem("counter") <- Counter) 
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
    <tenv> TEnv </tenv>
    <counter> Counter </counter>
    <subst> Subst </subst>
  [structural]
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
        <config>
          ---<k> K </k>
          <k> defaultKItem("K") </k>
          CfgItems1
        </config>
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

  syntax Map ::= defaultEnv ( Map )
  rule defaultEnv(X |-> _ Env) => X |-> ?var(X) defaultEnv(Env) [structural]
  rule defaultEnv(.Map) => .Map [ structural]

  rule
    <k> cleanFrameSubst(VarRoot) => .K <_/k>
    <subst> Subst => filterFrame!Subst(Subst, VarRoot) </subst>
  [structural]

  rule
    <k> cleanCallSubst(N) => .K <_/k>
    <subst> Subst => filterCallCoSkolemSubst(Subst) </subst>
  [structural]
endkm

