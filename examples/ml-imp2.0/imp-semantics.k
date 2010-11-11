load imp-syntax


kmod IMP-SEMANTICS is including IMP-DESUGARED-SYNTAX
  kvar N M N1 N2 : Nat
  kvar I J I1 I2 : Int++
  kvar Phi Phi1 Phi2 Psi Psi1 Psi2 : Formula
  kvar NtPhi : NtFormula
  kvar Subst Subst1 Subst2 : Subst
  kvar NzI : NzInt
  kvar V : Value
  kvar TV : TypedValue
  kvar X F : Id
  kvar E E1 E2 : Expression
  kvar T : ExpressionType
  kvar NvT : NvExpressionType
  kvar S S1 S2 : Statement
  kvar A A1 A2 : Annotation
  kvar K K1 K2 : K
  kvar KernelC Param : KernelC
  kvar KernelCList ParamList ArgList: List{KernelC}
  kvar Cfg : BagItem
  kvar Cfgs CfgItems CfgItems1 CfgItems2 PreCfgs PostCfgs : Bag
  kvar Map Env Env1 Env2 TEnv H : Map
  kvar Stack : List

  syntax K ::= KernelC
  syntax K ::= checkContracts
  syntax K ::= checkContract ( Id )
  syntax K ::= fieldList ( List{KernelC} )
  syntax TypedValue ::= newObject
  syntax MapItem ::= ExpressionType Id ( List{KernelC} ) : Bag => Bag
  syntax ListItem ::= callContext ( K , Map , Map )
  syntax BagItem ::= check ( KLabel )
                   | ( Nat feasible and Nat infeasible paths)
                     [format(g! d d d d d o)]

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

  macro check(Kl:KLabel) = <T>
                             <feasible> 0 </feasible>
                             <infeasible> 0 </infeasible>
                             <program> Kl(.List{K}) ~> checkContracts </program>
                             <spec> .Map </spec>
                             <struct> .Map </struct>
                             <fun> .Map </fun>
                             <tasks> .Bag </tasks>
                             <counter> 0 </counter>
                           </T>


***(
Output
***)
 rule
      <T_>
        <feasible> N </feasible>
        <infeasible> M </infeasible>
        <program> .K </program>
        <tasks> .Bag </tasks>
      <_/T>
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
Translation unit (top rule)
***)
  rule
    <program> translationUnit(KernelC) => KernelC <_/program>
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
    <program> T F(ParamList) S => .K <_/program>
    <spec_> .Map => T F(ParamList) |-> (S ~> return tv(void, unit)) <_/spec>
    <fun_> .Map => T F(ParamList) |-> (S ~> return tv(void, unit)) <_/fun>
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
Structure declaration
***)
  rule
    <program> struct X { KernelCList } ; => .K <_/program>
    <struct_> .Map => X |-> fieldList(KernelCList) <_/struct>
  [structural]


***(
Variable declaration
***)
  rule
    <k> T X ; => .K <_/k>
    <env_> .Map => X |-> FreeInt(N) <_/env>
    <tenv_> .Map =>  X |-> T <_/tenv>
    <counter> N => sNat N </counter>
  [structural]
 

***(
Statements
***)
  rule TV ; => .K [structural]
  rule block(KernelC) => KernelC [structural]
  rule if (tv(int, I) => tv(int, I) ? tv(int, 1) : tv(int, 0)) S1 else S2
  if notBool(I :: Int) [structural]
  rule if(tv(int, NzI)) S1 else S2 => S1 [structural]
  rule if(tv(int, 0)) S1 else S2 => S2 [structural]
  rule <k> while (E) S => 'if`(_`)_else_(E,, (S ~> while(E) S),, .K) <_/k>
  [structural]


***(
function call/return
***)
*** function call
  rule
    <spec_> T F(ParamList) |-> S <_/spec>
    <k>
        _`(_`)(F, ArgList) ~> K
      =>
        declParams(ParamList) ~> bindParams(ParamList, ArgList) ~> S
    </k>
    <stack_> .List => callContext(getReturnValue(T) ~> K, TEnv, Env) </stack>
    <tenv> TEnv => .Map </tenv>
    <env> Env => .Map </env>

*** return
  rule
    <k> return tv(_, V) ~> _ => K </k>
    <stack_> callContext(K, TEnv, Env) => .List </stack>
    <tenv> _ => TEnv </tenv>
    <env> _ => Env </env>
   <form> Phi => returns V /\ Phi </form>
  [structural]

*** retrieve the return value
  rule
    <k> getReturnValue(T) => tv(T, V) <_/k>
    <form> Phi /\ returns V => Phi </form>
  [structural]


***(
Expressions
***)
*** variable lookup
  rule
    <k> X => tv(T, V) <_/k>
    <env_> X |-> V <_/env>
    <tenv_> X |-> T <_/tenv>
  [structural]

*** unary expressions
  rule -tv(T, I) => tv(T, -Int I) [structural]
  rule !TV => TV ? tv(int, 0) : tv(int, 1) [structural]

*** referencing
  rule
    <k> &(tv(struct X *, I)->F) => tv(T *, I +Int listLen(KernelCList) )<_/k>
    <struct_>
      X |-> fieldList(KernelCList,,, (T F;),,, _)
    <_/struct>
  [structural]

*** dereferencing
  rule
    <k> *tv(T *, I) => derive(I) ~> load(T, I) <_/k> [structural]
  rule
    <k> tv(T, I)->F => *&(tv(T, I)->F) <_/k> [structural]
  
*** binary expressions
  rule tv(T, I1) + tv(T, I2) => tv(T, I1 +Int I2) [structural]
  rule tv(T *, I1) + tv(int, I2) => tv(T *, I1 +Int I2) [structural]
  rule tv(int, I1) + tv(T *, I2) => tv(T *, I1 +Int I2) [structural]
  rule tv(T, I1) - tv(T, I2) => tv(T, I1 -Int I2) [structural]
  rule tv(T *, I1) - tv(int, I2) => tv(T *, I1 -Int I2) [structural]
  rule tv(T *, I1) - tv(T *, I2) => tv(int, I1 -Int I2) [structural]  
  rule tv(T, I1) * tv(T, I2) => tv(T, I1 *Int I2) [structural]
  rule tv(T, I1) / tv(T, I2) => tv(T, I1 /Int I2) [structural]
  rule tv(T, I1) % tv(T, I2) => tv(T, I1 %Int I2) [structural]
  rule tv(T, I) << tv(int, N) => tv(T, I <<Int N) [structural]
  rule tv(T, I) >> tv(int, N) => tv(T, I >>Int N) [structural]
  rule tv(T, I1) >= tv(T, I2) => tv(int, bool2int(I1 >=Int I2)) [structural]
  rule tv(T, I1) > tv(T, I2) => tv(int, bool2int(I1 >Int I2)) [structural]
  rule tv(T, I1) <= tv(T, I2) => tv(int, bool2int(I1 <=Int I2)) [structural]
  rule tv(T, I1) < tv(T, I2) => tv(int, bool2int(I1 <Int I2)) [structural]
  rule tv(_, I1) == tv(_, I2) => tv(int, bool2int(I1 ==Int I2)) [structural]
  rule E1 != E2 => !(E1 == E2) [structural]
  rule TV && E => (TV ? E : tv(int, 0)) [structural]
  rule TV || E => (TV ? tv(int, 1) : E) [structural]
  

*** assignment expressions
  rule
    <k> X = tv(T, V) => tv(T, V) <_/k>
    <env_> X |-> (_ => V) <_/env>
  [structural]
  context (* [HOLE]) = _
  rule
    <k> *tv(T *, I) = tv(_, V) => derive(I) ~> store(T, I, V) <_/k>
  context ([HOLE] ->_) = _
  rule
    <k> tv(T, I)->F = E => *&(tv(T, I)->F) = E <_/k>
  [structural]
  rule E1 += E2 => E1 = (E1 + E2) [structural]
  rule E1 -= E2 => E1 = (E1 - E2) [structural]
  rule E1 *= E2 => E1 = (E1 * E2) [structural]
  rule E1 /= E2 => E1 = (E1 / E2) [structural]
  rule E1 %= E2 => E1 = (E1 % E2) [structural]
  rule E1 <<= E2 => E1 = (E1 << E2) [structural]
  rule E1 >>= E2 => E1 = (E1 >> E2) [structural]

  *** arm wresling the form
  rule
    <config>
      <form> Phi /\ @(-Int I +Int J >=Int 0) </form>
      CfgItems
    </config>
  =>
    <config>
      <form> Phi /\ (I === J) </form>
      CfgItems
    </config>
  
*** choice
  rule
    <config>
      <k> (tv(int, I) ? E1 : E2) ~> K </k>
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
  if notBool(I :: Int) [structural]
  rule tv(int, NzI) ? E1 : E2 => E1 [structural]
  rule tv(int, 0) ? E1 : E2 => E2 [structural]

*** cast
  rule (T) tv(_, V) => tv(T, V) [structural]

*** sizeof
  rule sizeof int => tv(int, 1) [structural]
  rule sizeof (T *) => tv(int, 1) [structural]
  rule
    <k> sizeof (struct X) => tv(int, listLen(KernelCList)) <_/k>
    <struct_> X |-> fieldList(KernelCList) <_/struct>
    [structural]


***(
Memory load, store and rearrangement
***)
  rule
    <k> derive(I) => .K <_/k>
    <heap_> I |-> _ : _ <_/heap>
  [structural]
***(
  rule
    <k> derive(I) <_/k>
    <form> NtPhi => FalseFormula </form>
  if check-sat(NtPhi) ==Bool "unsat"
***)
  rule
    <k> load(T, I) => tv(T, V) <_/k>
    <heap_> I |-> V : _ <_/heap>
  rule
    <k> store(T, I, V) => tv(T, V) <_/k>
    <heap_> I |-> (_ => V) : _ <_/heap>


***(
Memory management
***)
*** malloc/free
  rule malloc(TV) => newObject [structural]
  rule (T *) newObject => new T [structural]
  rule free(TV) => delete TV [structural]

*** new
  rule
    <k> new struct X => tv(struct X *, FreeInt(N)) <_/k>
    <heap_> .Map => initObject(FreeInt(N), X, KernelCList, sNat N) <_/heap>
    <struct_> X |-> fieldList(KernelCList) <_/struct>
    <counter> N => sNat N +Nat listLen(KernelCList) </counter>
  rule
    <k> new int => tv(int *, FreeInt(N)) <_/k>
    <heap_> .Map => FreeInt(N) |-> FreeInt(sNat N) <_/heap>
    <counter> N => sNat sNat N </counter>
  rule
    <k> new (T *) => tv(T **, FreeInt(N)) <_/k>
    <heap_> .Map => FreeInt(N) |-> FreeInt(sNat N) <_/heap>
    <counter> N => sNat sNat N </counter>

*** delete
  rule
    <k> delete tv(struct X *, I) => deleteObject(I, listLen(KernelCList)) <_/k>
    <struct_> X |-> fieldList(KernelCList) <_/struct>
  rule
    <k> delete tv(int *, I) => tv(void, unit) <_/k>
    <heap_> I |-> _ => .Map <_/heap>
  rule
    <k> delete tv(T **, I) => tv(void, unit) <_/k>
    <heap_> I |-> _ => .Map <_/heap>
  rule
    <k> deleteObject(I, (sNat N => N)) <_/k>
    <heap_> I +Int N |-> _ : _ => .Map <_/heap>
  rule
    <k> deleteObject(I, 1) => tv(void, unit) <_/k>
    <heap_> I |-> _ : _ => .Map <_/heap>


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


***(
Helpers
***)
  syntax K ::= declParams ( List{KernelC} )
  rule
    declParams(Param,,, ParamList) => Param ~> declParams(ParamList)
  [structural]
  rule declParams(.List{KernelC}) => .K [structural]

  syntax K ::= bindParams ( List{KernelC} , List{KernelC} )
  rule
      bindParams(((_ X;),,, ParamList), (TV,,, ArgList))
    =>
      (X = TV); ~> bindParams(ParamList, ArgList)
  [structural]
  rule bindParams(.List{KernelC}, .List{KernelC}) => .K [structural]

  syntax Nat ::= listLen ( List{KernelC} )
  rule listLen(_,,, KernelCList) => sNat listLen(KernelCList)
  [structural]
  rule listLen(.List{KernelC}) => 0 [structural]

  syntax Map ::= initObject ( Int++ , Id , List{KernelC} , Nat )
  rule
      initObject(I, X , (_ F;),,, KernelCList, N)
    =>
      I |-> FreeInt(N) : X . F initObject(I +Int 1, X , KernelCList, sNat N)
  [structural]
  rule initObject(_, _ , .List{KernelC}, _) => .Map [structural]
endkm

