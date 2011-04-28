kmod FOL is including MATCHC-SEMANTICS
--- FOL= is the proving heart of matching logic.  Provided that one had a "FOL= oracle" that can
--- prove any implications of the form "Pattern ===> Pattern1 Pattern2 ... PatternN" (the conclusion is a disjunction of patterns),
--- then one basically has a matching logic verifier.  Since we do not have such a magic oracle, we are going to mimic one.
--- We do it in a few steps.
  kvar CfgItems CfgItems1 CfgItems2 TaskItems : Bag
  kvar PEObj : PEMathObj
  kvar FEObj : FEMathObj
  kvar FreeObj : FreeMathObj
  kvar Obj Obj1 Obj2 : MathObj++
  kvar ObjList ObjList1 ObjList2 : List{MathObj++}
  kvar V1 V2 : Value
  kvar X : Id
  kvar N M : Nat
  kvar P : Int++
  kvar T : KLabel
  kvar List : List
  kvar PEList : PEListItem
  kvar FEList : FEListItem
  kvar FreeList : FreeListItem
  kvar Map : Map
  kvar PEMap : PEMapItem
  kvar FEMap : FEMapItem
  kvar FreeMap : FreeMapItem
  kvar HPN : HeapLabel
  kvar Env Env1 Env2 TEnv : Map
  kvar PEEnv : PEMapItem
  kvar FEEnv : FEMapItem
  kvar FreeEnv : FreeMapItem
  kvar H H1 H2 : Map
  kvar PEH : PEMapItem
  kvar FEH : FEMapItem
  kvar FreeH : FreeMapItem
  kvar PECfgItems : PEBagItem
  kvar FECfgItems : FEBagItem
  kvar FreeCfgItems : FreeBagItem
  kvar Set : Set
  kvar Phi Phi1 Phi2 : Formula
  kvar NtPhi NtPhi1 NtPhi2 : NtFormula
  kvar K : K
  kvar NeSubst : NeSubst
  kvar Subst : Subst
  kvar F : Field
  kvar Stack : List
  kvar CellLabel : CellLabel


***(
--- Step 1.2 : Eliminate a Map frame
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <CellLabel_> FreeMap => .Map <_/CellLabel>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <CellLabel_> FreeMap => .Map <_/CellLabel>
    <_/task>
  [structural]

--- Step 1.3 : Eliminate a locally bounded Map variable
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <CellLabel> Map => .Map </CellLabel>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <CellLabel> PEMap => .Map </CellLabel>
    <_/task>
  [structural]

--- Step 1.4 : Eliminate a globally bounded Map variable
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <CellLabel> Map => .Map </CellLabel>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <CellLabel> FEMap => .Map </CellLabel>
      <subst> Subst => Subst ;; (FEMap <- Map) </subst>
    <_/task>
  [structural]
***)
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <in> FreeList => .List <_/in>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <in> FreeList => .List <_/in>
    <_/task>
  [structural]

  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <in> List => .List </in>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <in> PEList => .List </in>
    <_/task>
  [structural]

  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <in> List => .List </in>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <in> FEList => .List </in>
      <subst> Subst => Subst ;; (FEList <- List) </subst>
    <_/task>
  [structural]


  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <out> FreeList => .List <_/out>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <out> FreeList => .List <_/out>
    <_/task>
  [structural]

  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <out> List => .List </out>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <out> PEList => .List </out>
    <_/task>
  [structural]

  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <out> List => .List </out>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <out> FEList => .List </out>
      <subst> Subst => Subst ;; (FEList <- List) </subst>
    <_/task>
  [structural]


  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <stack> FreeList => .List <_/stack>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <stack> FreeList => .List <_/stack>
    <_/task>
  [structural]

  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <stack> List => .List </stack>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <stack> PEList => .List </stack>
    <_/task>
  [structural]

***(
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <stack> List => .List </stack>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <stack> FEList => .List </stack>
      <subst> Subst => Subst ;; (FEList <- List) </subst>
    <_/task>
  [structural]
***)
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <stack> List => .List </stack>
    <_/task>
    <task>
      <taskType> Conclusion </taskType>
      <subst>
        Subst => applySubst(Subst, FEList <- List) ;; (FEList <- List)
      </subst>
      <config>
        <stack> FEList => .List </stack>
        (CfgItems => applySubst(CfgItems, FEList <- List))
      </config>
      (TaskItems => applySubst(TaskItems, FEList <- List))
    </task>
  [structural]


--- Step 1: Eliminate the environment and the return value
--- Step 1.1: Stepwise eliminate the environment
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <env_> X |-> Obj1 => .Map <_/env>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <env_> X |-> Obj2 => .Map <_/env>
      <form> Phi => Phi /\ Obj1 === Obj2 </form>
    <_/task>
  [structural]

--- Step 1.2 : Eliminate a env frame
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <env_> FreeEnv => .Map <_/env>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <env_> FreeEnv => .Map <_/env>
    <_/task>
  [structural]

--- Step 1.3 : Eliminate a locally bounded variable
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <env> Env => .Map </env>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <env> PEEnv => .Map </env>
    <_/task>
  [structural]

--- Step 1.4 : Eliminate a globally bounded variable
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <env> Env => .Map </env>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <env> FEEnv => .Map </env>
      <subst> Subst => Subst ;; (FEEnv <- Env) </subst>
    <_/task>
  [structural]


------ Step 1.5 : Eliminate the environment cell
---  rule
---    <task_>
---      <taskType> Hypothesis </taskType>
---      <env> .Map </env>
---    <_/task>
---    <task_>
---      <taskType> Conclusion </taskType>
---      <env> .Map </env>
---    <_/task>
---  [structural]


--- Step 2: Get rid of variable equalities and propagate them via substitution
--- Step 2.1 : Get rid of unbound variable equalities while executing the
--- configuration. Since the running configuration becomes the hypothesis,
--- is is safe to assume that there are no unbounded variable equalities left
--- in the hypothesis
---  rule
---    <task>
---      <taskType> Run </taskType>
---      <form> Phi => applySubst(Phi, NeSubst) </form>
---      <subst> Subst => applySubst(Subst, NeSubst) ;; NeSubst </subst>
---      (TaskItems => applySubst(TaskItems, NeSubst))
---    </task>
---  where NeSubst ::= getFreeSubstItem(Phi)
---  [structural]
  rule
    <task>
      <taskType> Run </taskType>
      <form> Phi => applySubst(Phi, getFreeSubstItem(Phi)) </form>
      <subst>
          Subst
        =>
          applySubst(Subst, getFreeSubstItem(Phi)) ;;
          filterAnonymousFreeSubst(getFreeSubstItem(Phi))
      </subst>
      (TaskItems => applySubst(TaskItems, getFreeSubstItem(Phi)))
    </task>
  if getFreeSubstItem(Phi) =/=Bool .Subst
  [structural]


--- Step 2.2 : Get rid of proof tasks for bound variables equalities in the
--- conclusion
---  rule
---    <task>
---      <taskType> Conclusion </taskType>
---      <form> Phi => applySubst(Phi, NeSubst) </form>
---      (TaskItems => applySubst(TaskItems, NeSubst))
---    </task>
---  where NeSubst ::= getPESubstItem(Phi)
---  [structural]
  rule
    <task>
      <taskType> Conclusion </taskType>
      <form> Phi => applySubst(Phi, getPESubstItem(Phi)) </form>
      (TaskItems => applySubst(TaskItems, getPESubstItem(Phi)))
    </task>
  if getPESubstItem(Phi) =/=Bool .Subst
  [structural]


--- Step 2.3 : Get rid of proof task for globally bound variable equalities in
--- the conclusion
---  rule
---    <task>
---      <taskType> Conclusion </taskType>
---      <form> Phi => applySubst(Phi, NeSubst) </form>
---      <subst> Subst => applySubst(Subst, NeSubst) ;; NeSubst </subst>
---      (TaskItems => applySubst(TaskItems, NeSubst))
---     </task>
---  where NeSubst ::= getFESubstItem(Phi)
  rule
    <task>
      <taskType> Conclusion </taskType>
      <form> Phi => applySubst(Phi, getFESubstItem(Phi)) </form>
      <subst>
        Subst => applySubst(Subst, getFESubstItem(Phi)) ;; getFESubstItem(Phi)
      </subst>
      (TaskItems => applySubst(TaskItems, getFESubstItem(Phi)))
     </task>
  if getFESubstItem(Phi) =/=Bool .Subst
  [structural]


--- Step 3: Stepwise, eliminate the heap, if any
--- Step 3.1: Eliminate a heap pattern
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <heap_> HPN(ObjList)(ObjList1) => .Map <_/heap>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <heap_> HPN(ObjList)(ObjList2) => .Map <_/heap>
      <form> Phi => Phi /\ ObjList1 === ObjList2 </form>
    <_/task>
  [structural]

--- Step 3.2 : Eliminate a location
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <heap_> P |-> V1 : F => .Map <_/heap>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <heap_> P |-> V2 : F => .Map <_/heap>
      <form> Phi => Phi /\ V1 === V2 </form>
    <_/task>
  [structural]

--- Step 3.3 : Eliminate a heap frame
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <heap_> FreeH => .Map <_/heap>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <heap_> FreeH => .Map <_/heap>
    <_/task>
  [structural]

--- Step 3.4 : Eliminate a bounded variable in the conclusion
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <heap> H => .Map </heap>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <heap> PEH => .Map </heap>
    <_/task>
  [structural]

--- Step 3.5 : Eliminate a globally bounded variable in the conclusion
  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <heap> H => .Map </heap>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <heap> FEH => .Map </heap>
      <subst> Subst => Subst ;; (FEH <- H) </subst>
    <_/task>
  [structural]

------ Step 3.6 : Eliminate the heap cell
---  rule
---    <task_>
---      <taskType> Hypothesis </taskType>
---      <heap> .Map </heap>
---    <_/task>
---    <task_>
---      <taskType> Conclusion </taskType>
---      <heap> .Map </heap>
---    <_/task>
---  [structural]


  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <in> stream(Obj1) => .List </in>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <in> stream(Obj2) => .List </in>
      <form> Phi => Phi /\ Obj1 === Obj2 </form>
    <_/task>
  [structural]

  rule
    <task_>
      <taskType> Hypothesis </taskType>
      <out> stream(Obj1) => .List </out>
    <_/task>
    <task_>
      <taskType> Conclusion </taskType>
      <out> stream(Obj2) => .List </out>
      <form> Phi => Phi /\ Obj1 === Obj2 </form>
    <_/task>
  [structural]


--- Step 5: Get rid of the formula implication task
  rule
      <task_>
        <taskType> Hypothesis </taskType>
        <config_>
          <env> .Map </env>
          <heap> .Map </heap>
          <stack> .List </out>
          <in> .List </in>
          <out> .List </out>
        <_/config>
        <form> Phi1 </form>
      <_/task>
      <task_>
        <taskType> Conclusion </taskType>
        <config_>
          <env> .Map </env>
          <heap> .Map </heap>
          <stack> .List </out>
          <in> .List </in>
          <out> .List </out>
        <_/config>
        <form> Phi2 </form>
        <subst> Subst </subst>
      <_/task>
    =>
      <task_>
        <taskType> Constrain </taskType>
        <config> .Bag </config>
        <form> Phi1 ===> Phi2 </form>
        <subst> Subst </subst>
      <_/task>
  [structural print Phi1 "\n===>\n" Phi2]
  ---[structural]


--- Step 6: Call external SMT solver to check the formula if the "in-house"
--- approach failed
  rule
    <task_>
      <taskType> Constrain </taskType>
      <form> NtPhi => TrueFormula </form>
    <_/task> 
  if check-validity(NtPhi)
  [structural]
endkm

