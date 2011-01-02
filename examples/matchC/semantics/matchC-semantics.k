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
  kvar ParamList ArgList: List{KernelC}
  kvar CfgItems CfgItems1 CfgItems2 TaskItems : Bag 
  kvar Pattern Pattern1 Pattern2 PrePattern PostPattern : Pattern
  kvar Env TEnv StructMap FunMap : Map
  kvar Stack : List
  kvar checkSet Set : Set


  syntax K ::= checkContracts
             | checkContract ( Id )
             | uncheckContract ( Id )

  syntax K ::= `Run
             | `Hypothesis
             | `Conclusion
             | `Constrain

  configuration <top> 
                  <feasible> 0 </feasible>
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
        T F(ParamList) /*@ pre PrePattern */ /*@ post PostPattern */ |-> S
        FunMap
      </fun>
    <_/task>
    (
      .Bag
    =>
      <task_>
        <struct> StructMap </struct>
        <fun>
          T F(ParamList) /*@ pre PrePattern */ /*@ post PostPattern */ |-> S
          FunMap
        </fun>
        <k> declParams(ParamList) ~> /*@ assume PrePattern */ ~> S </k>
        <stack> callContext(/*@ assert PostPattern */, .Map, .Map) </stack>
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
        <k> declParams(ParamList) ~> S </k>
        <stack> callContext(.K, .Map, .Map) </stack>
      <_/task>
    )
  [structural]


***(
Function definition/declaration
***)
  rule
    <program>
      T F(ParamList) /*@ pre PrePattern */ /*@ post PostPattern */ => .K
    <_/program>
    <fun_>
        .Map
      =>
        T F(ParamList) /*@ pre PrePattern */ /*@ post PostPattern */ |-> .K
    <_/fun>
  [structural]
  rule
    <program>
      T F(ParamList) /*@ pre PrePattern */ /*@ post PostPattern */ S => .K
    <_/program>
    <fun_>
        .Map
      =>
        T F(ParamList) /*@ pre PrePattern */ /*@ post PostPattern */
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
  if notBool isInt(I) [structural]


***(
summary function calls
***)
  rule
    <fun_>
      T F(ParamList) /*@ pre PrePattern */ /*@ post PostPattern */ |-> _
    <_/fun>
    <k>
        _`(_`)(F, ArgList) ~> K
      =>
        declParams(ParamList)
        ~> bindParams(ParamList, ArgList)
        ~> /*@ assert co-skolemize(N, PrePattern) */
        ~> /*@ assume co-skolemize(N, PostPattern) */
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
        /*@ invariant Pattern */
        ~> while (E) S ~> K
      =>
        /*@ assert Pattern */
        ~> 'if`(_`)_else_(E,, (S ~> /*@ assert Pattern */),, K)
    </k>

***(
assumed patterns
  1. are merged with the current configuration
  2. split the current configuration if they contain disjunctions
***)
  rule
    <task>
      <config>
        <k> /*@ assume Pattern1 \/ Pattern2 */ ~> K </k>
        CfgItems
      </config>
      TaskItems
    </task>
  =>
    <task>
      <config>
        <k> /*@ assume Pattern1 */  ~> K </k>
        CfgItems
      </config>
      TaskItems
    </task>
    <task>
      <config>
        <k> /*@ assume Pattern2 */ ~> K </k>
        CfgItems
      </config>
      TaskItems
    </task>
  [structural]
  rule
    <task>
      <config> 
        <k> /*@ assume <config> CfgItems </config> /\ Phi2 */ => .K <_/k>
        <program> .K </program>
        <struct> StructMap </struct>
        <fun> FunMap</fun>
        <tenv> TEnv </tenv>
        <counter> N </counter>
        (_ => skolemize(N, applySubst(CfgItems, Subst)))
      </config>
      <form> Phi1 => Phi1 /\ skolemize(N, applySubst(Phi2, Subst)) </form>
      <subst> Subst </subst>
    </task>
    <other-counter> N => sNat N </other-counter>

***(
asserted patterns
  1. must be matched the current configuration, that is, the implication
     current configuration ===> asserted patterns can rewrite to true (the rule
     searches for the existance of a proof in the side condition, and also
     returns facts found out to be true during the search for a proof)
  2. may be assumed correct afterward
  3. split the current configuration if they contain disjunctions
***)
  rule
    <task>
      <config>
        <k> /*@ assert Pattern1 \/ Pattern2 */ ~> K </k>
        CfgItems
      </config>
      TaskItems
    </task>
  =>
    <task>
      <config>
        <k> /*@ assert Pattern1 */  ~> K </k>
        CfgItems
      </config>
      TaskItems
    </task>
    <task>
      <config>
        <k> /*@ assert Pattern2 */ ~> K </k>
        CfgItems
      </config>
      TaskItems
    </task>
  [structural]
  rule
    <task>
      <taskType> Run </taskType>
      <config>
        <k>
            /*@ assert <config> CfgItems2 </config> /\ Phi */
          =>
            /*@ assume <config> CfgItems2 </config> /\ Phi */
        <_/k>
        <program> .K </program>
        <struct> StructMap </struct>
        <fun> FunMap</fun>
        <tenv> TEnv </tenv>
        <counter> N </counter> 
        CfgItems1
      </config>
      <subst> Subst1 => Subst2 </subst>
      TaskItems
    </task>
    <other-counter> N </other-counter>
  if search(
      <task>
        <taskType> Hypothesis </taskType>
        <config> CfgItems1 </config>
        <subst> Subst1 </subst>
        TaskItems
      </task>
      <task>
        <taskType> Conclusion </taskType>
        <config> CfgItems2 </config>
        <form> Phi </form>
        <subst> .Subst </subst>
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
endkm

