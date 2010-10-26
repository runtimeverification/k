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
  kvar K : K
  kvar KernelC : KernelC
  kvar KernelCList KernelCList1 KernelCList2 : List{KernelC}
  kvar Cfg : BagItem
  kvar Cfgs CfgItems CfgItems1 CfgItems2 PreCfgs PostCfgs : Bag
  kvar Map Env Env1 Env2 TEnv H : Map

  syntax K ::= KernelC
  syntax K ::= checkContracts | checkContracts ( Map ) | checkContract ( Id )
  syntax K ::= fieldList ( List{KernelC} )
  syntax TypedValue ::= newObject
  syntax MapItem ::= ExpressionType Id ( List{KernelC} ) : Bag => Bag
  syntax  BagItem ::= check ( KLabel )
                    | ( Nat feasible and Nat infeasible paths)
                      [format(g! d d d d d o)]

  configuration <T> 
                  <feasible> 0 </feasible>
                  <infeasible> 0 </infeasible>
                  <spec> .Map </spec>
                  <struct> .Map </struct>
                  <fun> .Map </fun>
                  <counter> 0 </counter>
                  <config>
                    <k> .K </k>
                    <tenv> .Map </tenv>
                    <env> .Map </env>
                    <heap> .Map </heap>
                    <form> TrueFormula </form>
                    <subst> .Subst </subst>
                  </config>
                </T>

  macro check(Kl:KLabel) = <T>
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


***(
Translation unit (top rule)
***)
  rule
    <k> translationUnit(KernelC) => KernelC ~> checkContracts <_/k>
  [structural]
  rule
    <k> checkContracts => checkContracts(Map) <_/k>
    <fun> Map </fun>
  [structural]
  rule
    checkContracts((X |-> _) Map) => checkContract(X) ~> checkContracts(Map)
  [structural]
  rule checkContracts(.Map) => .K [structural]


***(
Function definition/declaration
***)
  rule
    <k> T F(KernelCList) /*@ pre PreCfgs */ /*@ post PostCfgs */ => .K <_/k>
    <spec_> .Map => T F(KernelCList) : PreCfgs => PostCfgs <_/spec>
  rule
    <k> T F(KernelCList) /*@ pre PreCfgs */ /*@ post PostCfgs */ S => .K <_/k>
    <spec_> .Map => T F(KernelCList) : PreCfgs => PostCfgs <_/spec>
    <fun_> .Map => F |-> T F(KernelCList) S <_/fun>    


***(
Structure declaration
***)
  rule
    <k> struct X { KernelCList } ; => .K <_/k>
    <struct_>
      .Map => X |-> fieldList(KernelCList)
    <_/struct>

***(
Function entry
***)
  rule
    <k>
        checkContract(F)
      =>
        /*@ assume PreCfgs */
        ~> S
        ~> functionEnd
        ~> /*@ assert PostCfgs */
    <_/k>
    <tenv> _ => bindTEnv(KernelCList) </tenv>
    <env> _ => .Map </env>
    <heap> _ => .Map </heap>
    <form> _ => TrueFormula </form>
    <subst> _ => .Subst </subst>
    <fun_> F |-> T F(KernelCList) S <_/fun>
    <spec_> T F(KernelCList) : PreCfgs => PostCfgs <_/spec>
  [structural]

***(
Output
***)
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


***(
Variable declaration
***)
  rule
    <k> T X ; => .K <_/k>
    <env_> .Map => X |-> ?Int(N) <_/env>
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
  rule
    <k> return tv(_, V) ~> K ~> functionEnd => .K <_/k>
    <form> Phi => returns V /\ Phi </form>
  rule
    <k> functionEnd => .K <_/k>
    <form> Phi => returns unit /\ Phi </form>


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
    <k> &(tv(struct X *, I)->F) => tv(T *, I +Int listLen(KernelCList1) )<_/k>
    <struct_>
      X |-> fieldList(KernelCList1,,, (T F;) ,,, KernelCList2)
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
  rule TV && E => (TV ? E : tv(int, 0))
  [structural]
  rule TV || E => (TV ? tv(int, 1) : E)
  [structural]

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
  --- FIXME
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
Memory malloc/free
***)
  rule malloc(TV) => newObject [structural]
  rule (T *) newObject => new T [structural]
  rule free(TV) => delete TV [structural]

***(
Memory new/delete
***)
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
  rule
    <k> delete tv(struct X *, I) => deleteObject(I, listLen(KernelCList)) <_/k>
    <struct_> X |-> fieldList(KernelCList) <_/struct>
  rule
    <k> deleteObject(I, (sNat N => N)) <_/k>
    <heap_> I +Int N |-> _ : _ => .Map <_/heap>
  rule
    <k> deleteObject(I, 1) => tv(void, unit) <_/k>
    <heap_> I |-> _ : _ => .Map <_/heap>
  rule
    <k> delete tv(int *, I) => tv(void, unit) <_/k>
    <heap_> I |-> _ => .Map <_/heap>
  rule
    <k> delete tv(T **, I) => tv(void, unit) <_/k>
    <heap_> I |-> _ => .Map <_/heap>


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
      <form> Phi1 </form>
      <subst> Subst </subst>
      <tenv> TEnv </tenv>
    <_/config>
    (
      .Bag
    =>
      <config>
        <k> K </k>
        ---applySubst(skolemize(N, <form> Phi1 /\ Phi2 </form> CfgItems), Subst)
        skolemize(N, applySubst(<form> Phi1 /\ Phi2 </form> CfgItems, Subst))
        skolemize(N, <subst> Subst </subst>)
        <tenv> TEnv </tenv>
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
    <config_>
      <k> /*@ assert Cfgs */ => /*@ assume Cfgs */ <_/k>
      <env> Env </env>
      <heap> H </heap>
      <form> Phi </form>
      ---(<subst> Subst1 </subst> => skolemize(N, <subst> Subst2 </subst>))
      <subst> Subst1 => Subst2 </subst>
    <_/config>
    <counter> N </counter>
  if search(
      <config>
        <env> Env </env>
        <heap> H </heap>
        <form> Phi </form>
        <subst> Subst1 </subst>
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
function calls
***)
  rule
    <spec_> T F(KernelCList1) : PreCfgs => PostCfgs <_/spec>
    <config_>
      <k>
          _`(_`)(F, KernelCList2)
        =>
          /*@ assert co-skolemize(PreCfgs) */
          ~> /*@ assume co-skolemize(PostCfgs) */
          ~> restoreContext(TEnv, Env, Subst)
          ~> getReturnValue(T)
      <_/k>
      <tenv> TEnv => bindTEnv(KernelCList1) </tenv>
      <env> Env => bindEnv(KernelCList1, KernelCList2) </env>
      <heap> H </heap>
      <form> Phi </form> 
      <subst> Subst </subst>  
    <_/config>
***(
  if search(
    <config>
      <env> bindEnv(KernelCList1, KernelCList2) </env>
      <heap> H </heap>
      <form> Phi </form>
      <subst> Subst1 </subst>
      <newImpl> N </newImpl>
    </config>
    ===>
    co-skolemize(PreCfgs)
  =>
    <config>
      <form> TrueFormula </form>
      <subst> Subst2 </subst>
    </config>
  )
***)
  rule
    <k> restoreContext(TEnv, Env, Subst) => .K <_/k>
    <tenv> _ => TEnv </tenv>
    <env> _ => Env </env>
    <subst> _ => Subst </subst>
  [structural]

***(
retrieve the return value
***)  
  rule
    <k> getReturnValue(NvT) => tv(NvT, V) <_/k>
    <form> Phi /\ returns V => Phi </form>
  [structural]
  rule getReturnValue(void) => tv(void, unit) [structural]


  syntax Nat ::= listLen ( List{KernelC} )
  rule listLen(_,,, KernelCList) => sNat listLen(KernelCList)
  [structural]
  rule listLen(.List{KernelC}) => 0 [structural]

  syntax Map ::= bindTEnv ( List{KernelC} )
  rule bindTEnv((T X;),,, KernelCList) => X |-> T bindTEnv(KernelCList)
  [structural]
  rule bindTEnv(.List{KernelC}) => .Map [structural]

  syntax Map ::= bindEnv ( List{KernelC} , List{KernelC} )
  rule
      bindEnv(((T X;),,, KernelCList1), (tv(_, V),,, KernelCList2))
    =>
      X |-> V bindEnv(KernelCList1, KernelCList2)
  [structural]
  rule bindEnv(.List{KernelC}, .List{KernelC}) => .Map [structural]

  syntax Map ::= initObject ( Int++ , Id , List{KernelC} , Nat )
  rule
      initObject(I, X , (_ F;),,, KernelCList, N)
    =>
      I |-> FreeInt(N) : X . F initObject(I +Int 1, X , KernelCList, sNat N)
  [structural]
  rule initObject(_, _ , .List{KernelC}, _) => .Map [structural]
endkm

