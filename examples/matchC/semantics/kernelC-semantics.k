kmod KERNELC-SEMANTICS is including KERNELC-DESUGARED-SYNTAX
  kvar N : Nat
  kvar I J I1 I2 : Int++
  kvar Phi : Formula
  kvar NzI : NzInt
  kvar V : Value
  kvar TV : TypedValue
  kvar X F : Id
  kvar E E1 E2 : Expression
  kvar T : ExpressionType
  kvar NvT : NvExpressionType
  kvar S S1 S2 : Statement
  kvar K K1 K2 : K
  kvar KernelC Param : KernelC
  kvar KernelCList ParamList ArgList: List{KernelC}
  kvar Map Env TEnv : Map
  kvar Stack : List

  syntax K ::= KernelC
  syntax KResult ::= String
  syntax K ::= checkContracts
  syntax K ::= runMain
  syntax K ::= checkContract ( Id )
  syntax K ::= fieldList ( List{KernelC} )
  syntax TypedValue ::= newObject
  syntax ListItem ::= callContext ( K , Map , Map )


  configuration <T> 
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
                    </config*>
                  </tasks>

                  <in> .List </in>
                  <out> .List </out>

                  <counter> 0 </counter>
                </T>


***(
Function entry
***)
  rule
    <program> runMain => .K <_/program>
    <fun_> T main(.List{KernelC}) |-> S <_/fun>
    <tasks>
        _
      =>
        <config_>
          <k> S </k>
          <stack> callContext(.K, .Map, .Map) </stack>
        <_/config>
    </tasks>
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
    <program> T F(ParamList) S => .K <_/program>
    <spec_> .Map => T F(ParamList) |-> (S ~> return tv(void, unit)) <_/spec>
    <fun_> .Map => T F(ParamList) |-> (S ~> return tv(void, unit)) <_/fun>
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
  rule if(tv(_, NzI)) S1 else S2 => S1 [structural]
  rule if(tv(_, 0)) S1 else S2 => S2 [structural]
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
    <k> *tv(T *, I) => derive(I) ~> load(T, I) <_/k>
  [structural]
  rule
    <k> tv(T, I)->F => *&(tv(T, I)->F) <_/k>
  [structural]
  
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

*** assignment
  rule
    <k> X = tv(T, V) => tv(T, V) <_/k>
    <env_> X |-> (_ => V) <_/env>
  [structural]
  context (* [HOLE]) = _
  rule
    <k> *tv(T *, I) = tv(_, V) => derive(I) ~> store(T, I, V) <_/k>
  [structural]
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

*** selection
  rule tv(_, NzI) ? E1 : E2 => E1 [structural]
  rule tv(_, 0) ? E1 : E2 => E2 [structural]

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
    <k>
        delete tv(struct X *, I)
      =>
        derive(I) ~> deleteObject(I, listLen(KernelCList))
    <_/k>
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


***(
I/O
***)
  rule
    <k> printf(_:String,,,tv(_,I)) => tv(void, unit) <_/k>
    <out_> .List => ListItem(I) </out>
  [structural]
  rule printf(_:String) => tv(void, unit) [structural]


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

