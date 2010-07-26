load imp-syntax


kmod IMP-SEMANTICS is including IMP-DESUGARED-SYNTAX
  kvar M N N1 N2 : Nat
  kvar I J I1 I2 : Int++
  kvar NzI : NzInt
  kvar T : ExpType
  kvar NvT : NvExpType
  kvar F X Sn Fld : Id
  kvar Xl : List{Id}
  kvar V : Val
  kvar Vl : List{Val}
  kvar E E' E1 E2 : Exp
  kvar El El' : List{Exp}
  kvar S S1 S2 : Stmt
  kvar Ss : Stmts
  kvar K : K
  kvar NeK : NeK
  kvar L : KLabel
  kvar Phi Phi' : Formula
  kvar NtPhi : NtFormula
  kvar Subst Subst' : Subst
  kvar Env Env' : Map
  kvar Cfg : BagItem
  kvar Cfgs Cfgs' CfgItems : Bag

  syntax Builtins ::= Int++ | ExpType
  syntax KResult ::= Int++ | List{Val} | ExpType 
  syntax K ::= DeclAnnot | Stmts | List{Exp} 

  syntax Exp ::=
                 load ( Int++ )
---               | store ( Int++ , Exp ) [strict]
               | store ( Exp , Exp ) [strict]

---  op __`(_`):_=>_ : ExpType Id List{Id} Bag Bag -> MapItem

  syntax MapItem ::= ExpType Id ( Stmts ) : Bag => Bag 

  configuration <T> 
                  <feasible > 0 </feasible>
                  <infeasible > 0 </infeasible>
                  <spec> .Map </spec>
                  <config>
                    <k> .K </k>
                    <struct>.Map</struct>
                    <env> .Map </env>
                    <heap> .Map </heap>
                    <form> TrueFormula </form>
                    <subst> .Subst </subst>
                    <newSym> 0 </newSym>
                    <newImpl> 0 </newImpl>
                  </config>
                </T>

--- computing the list of fields 
  syntax List ::= struct2list ( K , Int )
  macro struct2list(T Fld; ~> Ss, Offset:Int) = [Fld, T, Offset] struct2list(Ss, Offset +Int 1)
  macro struct2list(T Fld;, Offset) = [Fld, T, Offset]

--- scalar types
  syntax Bool ::= isScalar ( ExpType )
  macro isScalar(int) = true
  macro isScalar(& T) = true 
  macro isScalar(struct Sn) = false

--- default values
  syntax Val ::= defaultVal ( ExpType )
  macro defaultVal(int) = 0
  macro defaultVal(& T) = 0

--- heap allocation/deallocation
  syntax K ::= allocHeap ( List ) | deallocHeap ( Int++ , Int++ )

--- translate a pair (TXl, Vl) into a map Xi |-> [Vi, Ti]
  syntax Map ::= map ( Stmts , List{Exp} )
  macro map(noneStmts, .List{Id}) = .Map
  macro map(__;(T, X), V) = (X |-> [V, T])
  macro map(__;(T, *X), V) = (X |-> [V, &T])
  macro map((__;(T, X)  TXl:Stmts), (V ,,, Vl)) = (X |-> [V, T]) map(TXl, Vl)
  macro map((__;(T, *X)  TXl:Stmts), (V ,,, Vl)) = (X |-> [V, &T]) map(TXl, Vl)


  rule I1 + I2 => I1 +Int I2
  rule _-_(I1, I2) => _-Int_(I1, I2)
  rule _*_(I1, I2) => I1 *Int I2
  rule I1 / I2 => I1 /Int I2
  rule I1 % I2 => I1 %Int I2
  rule - I => -Int I
  rule I1 >= I2 => ?_(I1 >=Int I2)
  rule I1 > I2 => ?_(I1 >Int I2)
  rule I1 <= I2 => ?_(I1 <=Int I2)
  rule I1 < I2 => ?_(I1 <Int I2)
  rule I1 == I2 => ?_(I1 ==Int I2)

  rule I && E => (I ? 1 : 0) && E if notBool(I :: Int) [metadata "structural"]
  rule NzI && E => E
  rule 0 && E => 0
  rule I || E => (I ? 1 : 0) || E if notBool(I :: Int) [metadata "structural"]
  rule NzI || E => NzI
  rule 0 || E => E
  rule ! I => I ? 0 : 1 if notBool(I :: Int) [metadata "structural"]
  rule ! NzI => 1
  rule ! 0 => 1

  rule
    < config >
      < k > (I ? E1 : E2) ~> K </ k >
      < form > Phi </ form >
      CfgItems
    </ config >
  =>
    < config >
      < k > E1 ~> K </ k >
      < form > Phi /\ ~(I === 0) </ form >
      CfgItems
    </ config >
    < config >
      < k > E2 ~> K </ k >
      < form > Phi /\ I === 0 </ form >
      CfgItems
    </config>
  rule NzI ? E1 : E2 => E1
  rule 0 ? E1 : E2 => E2

--- struct declaration

  rule <k> struct_`{_`};(Sn, Ss) => .K <_/k>
       <struct_> .Map => (Sn |-> struct2list(Ss, 0)) <_/struct>

--- variable declaration

  rule
---    <k> int Xl ; => .K <_/k>
---    <env_> .Map => Xl |-> range(N, length,,,(Xl)) <_/env>
---    <newSym> N => N +Int length,,,(Xl) </newSym>
    <k> T X; => .K <_/k>
    <env> .Map => X |-> [defaultVal(T), T] <_/env>

  rule I ; => .K [metadata "structural"]
  rule {} => .K [metadata "structural"]
  rule { Ss } => Ss [metadata "structural"]
  rule S1 S2 => S1 ~> S2 [metadata "structural"]

--- simple variable evaluation
  rule
    <k> X => I <_/k> 
---    <env_> X |-> I <_/env>
    <env_> X |-> [I, T] <_/env>
--- struct field evaluation 
---    the struct values are stored only in the heap
---    for the moment we do not consider "static" struct values", i.e., only
---      declarations of the form "struct name *v;" are allowed
  rule
    <k> Var:Var->Fld => *(I +Int J) <_/k> 
    <env_> X |-> [I, &struct Sn] <_/env>
    <struct_> Sn |-> (_ [Fld, T, J] _) <_/struct>

--- the evaluation of the new operator
  rule
    <k> new T => allocHeap([@scalar, T, 0]) ~> N <_/k>
    <newSym> N </newSym>
    if isScalar(T) ==Bool true
  rule
    <k> new struct Sn => allocHeap(Fl) ~> N <_/k>
    <struct_> Sn |-> Fl <_/struct>
    <newSym> N </newSym>
  rule
    <k> allocHeap(.List) => . <_/k>
  rule
    <k> allocHeap([Fld, T, J] Fl:List) => allocHeap(Fl) <_/k>
    <heap_> . => N |-> defaultVal(T) : [Fld, T] </heap>
    <newSym> N => N +Int 1 </newSym>

--- delete statement processing
  rule
    <k> delete I; => deallocHeap(I, length(Fl)) <_/k>
    <env_> _ |-> [(I => 0), &struct Sn] <_/env>
    <struct_> Sn |-> Fl <_/struct>
  rule
    <k> deallocHeap(I, M) => deallocHeap(I +Int 1, M +Int -1) <_/k>
    <heap_> (I |-> _:[_, _]) => . </heap>
    if M >Int 0 
  rule
    <k> deallocHeap(I, 0) => . <_/k>
    

--- assignment to a simple variable
  rule
    <k> X = V ; => .K <_/k>
    <env_> (X |-> [_, T]) => (X |-> [V, T]) <_/env>

--- assignment to a struct field
  context ( [HOLE] ->_) = _ ;
  rule
    <k> (I->Fld = V ;) => *(I+J) = V; <_/k>
    <env_> _ |-> [I, &struct Sn] <_/env>
    <struct_> Sn |-> (_ [Fld, T, J] _) <_/struct>

--- dereferencing 
  rule <k> * I => derive(I) ~> load(I) <_/k>
      [structural]
  context (* [HOLE]) = _ ;
  rule <k> (* I) = J ; => derive(I) ~> store(I, J) <_/k>
  [metadata "structural"]
  rule
    <k> derive(I) => .K <_/k>
    <heap_> I |-> J : [Fld, T] <_/heap>
  [metadata "structural"]
  rule
    <k> derive(I) <_/k>
    <form> NtPhi => FalseFormula </form>
  if check-sat(NtPhi) ==Bool "unsat" 
  rule
    <k> load(I) => J <_/k>
    <heap_> I |-> J:[Fld, T] <_/heap>
  rule
    <k> store(I, J) => .K <_/k>
    <heap_> (I |-> _:[Fld, T]) => (I |-> J:[Fld, T]) <_/heap>
  rule
    <k> return; ~> K ~> functionEnd => .K <_/k>
  rule
    <k> return I ; ~> K ~> functionEnd => .K <_/k>
    <form> Phi => Phi /\ ?return(I) </form>
  rule
    <k> functionEnd => .K <_/k>

  rule if (I) S1 else S2 => if (I ? 1 : 0) S1 else S2 if notBool(I :: Int)
  [metadata "structural"]
  rule if (NzI) S else _ => S
  rule if (0) _ else S => S

  rule
    <k>
      (// invariant Cfgs ~> while (E) S ~> K)
    =>
      (// assert Cfgs ~> 'if`(_`)_else_(E,, { S // assert Cfgs },, K))
    </k>
  [metadata "structural"]

  rule
    <config_> 
      <k>
        // assume
          <config>
            <env> Env' </env>
            <form> Phi' </form>
            CfgItems
          </config>
          Cfgs
        ~> K
      =>
        // assume Cfgs ~> K
      </k>
      <env> Env </env>
      <form> Phi </form>
      <subst> Subst </subst>
      <newSym> M </newSym>
      <newImpl> N </newImpl>
    <_/config>
    (
      .Bag
    =>
      <config>
        <k> K </k>
        (
          <env> Env[Env'] </env>
          <form> Phi /\ Phi' </form>
          CfgItems
        )[Subst]
        <subst> Subst </subst>
        <newSym> M </newSym>
        <newImpl> N </newImpl>
      </config>
    )
  [metadata "structural"]
  rule <config_> <k> // assume .Bag <_/k> <_/config> => .Bag
  [metadata "structural"]

  rule
    <config>
      <k> // assert Cfgs => // assume Cfgs <_/k>
      <subst> Subst => Subst' </subst>
      <newSym> M </newSym>
      <newImpl> N => sNat N </newImpl>
      (CfgItems => skolemize(N, CfgItems))
    </config>
  if search(
    <config>
      <subst> Subst </subst>
      <newImpl> N </newImpl>
      CfgItems
    </config>
    ===>
    Cfgs
  =>
    <config>
      <form> TrueFormula </form>
      <subst> Subst' </subst>
    </config>
  )


  rule
    <spec_> T F(TXl) : Cfgs => Cfgs' <_/spec>
    <config>
      <k> _`(_`)(F, Vl) => // assume Cfgs'[Subst'] ~> getReturnValue(T) <_/k>
      (<env> Env </env> => skolemize(N, <env> Env </env>))
      <subst> Subst </subst>
      <newSym> M </newSym>
      <newImpl> N => sNat N </newImpl>
      (CfgItems => skolemize(N, CfgItems))
    </config>
  if search(
    <config>
      <env> map(TXl, Vl) </env>
      <subst> Subst </subst>
      <newImpl> N </newImpl>
      CfgItems
    </config>
    ===>
    Cfgs
  =>
    <config>
      <form> TrueFormula </form>
      <subst> Subst' </subst>
    </config>
  )
  rule
    <k> getReturnValue(NvT) => I <_/k>
    <form> Phi /\ ?return(I) => Phi </form>
  [metadata "structural"]
  rule <k> getReturnValue(void) => NULL <_/k> [metadata "structural"]

  rule
    <k>
        __`(_`)_`{_`}(T, F, TXl, (//pre Cfgs //post Cfgs'), Ss)
      =>
        //assume Cfgs ~> Ss ~> functionEnd ~> //assert Cfgs'
    <_/k>


  op mkSpec : K -> Map
  rule
      mkSpec((__`(_`)_`{_`}(T, F, TXl, (//pre Cfgs //post Cfgs'), Ss) ~> K))
    =>
      T F(TXl) : co-skolemize(Cfgs) => co-skolemize(rmEnv(Cfgs')) mkSpec(K)
  [metadata "structural"]
  rule mkSpec(.K) => .Map [metadata "structural"]

  op rmEnv : Bag -> Bag
  rule
      rmEnv(<config> <env> Env </env> CfgItems </config> Cfgs)
    =>
      <config> <env> .Map </env> CfgItems </config> rmEnv(Cfgs)
  [metadata "structural"]
  rule rmEnv(.Bag) => .Bag [metadata "structural"]

  rule (E,,, El) |-> (E',,, El') => (E |-> E') (El |-> El') [metadata "structural"]
  rule .List{Id} |-> .List{Id} => .Map [metadata "structural"]

  op length`,`,`,_ : List{Exp} -> Nat
  rule length,,,(X,,, Xl) => sNat length,,,(Xl) [metadata "structural"]
  rule length,,,(.List{Id}) => 0 [metadata "structural"]

  op range : Nat Nat -> List{Val}
  rule range(N, sNat(M)) => ?Int(N),,, range(sNat N, M) [metadata "structural"]
  rule range(N, 0) => .List{Id} [metadata "structural"]
endkm

