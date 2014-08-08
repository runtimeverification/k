module KERNELC-POINTER
  imports KERNELC-SYNTAX

  syntax Pointer ::= "ObjectPointer" "(" Type "," Int ")"
                   | "MemberPointer" "(" Type "," Int "," Id ")"
                   | "Null"
endmodule

module KERNELC-SEMANTICS
  imports KERNELC-SYNTAX
  imports KERNELC-POINTER 

  /*
   * Macros
   */
  rule if (E:Expression) S:Statement => if (E) S else ;    [macro]

  /*
   * KernelC configuration 
   */
  configuration
    <config> 
      <struct> .Map </struct>
      <fun> .Map </fun>

      <k> $PGM:File ~> main(.Expressions) </k>
      <env> .Map </env>
      <stack> .List </stack>
      <fname> .K </fname>
      <tenv> .Map </tenv>
                  
      <heap> .Map </heap>

      <in> .List </in>
      <out> .List </out>

      <counter> 0 </counter>
    </config>

  syntax Expression ::= Value
  syntax Value ::= Int | Pointer

*** memory management
                      | new Type
                      | delete Expression [strict]
*** extra stuff, not part of the language syntax, but helpful for the semantics
                      | ExpressionHelper
  syntax ExpressionHelper ::= load ( Type , Value )
                            | store ( Type , Value , Value )
                            | read ( Type )
                            | offset ( Type , Id )
                            | new Type
                            | detele TypedValue
                            | deleteObject ( Value , Nat )




  kvar N : Nat
  kvar I J I1 I2 : Int++
  kvar Phi : Formula
  kvar NzI : NzInt
  kvar V : Value
  kvar TV : TypedValue
  kvar X F FName : Id
  kvar E E1 E2 : Expression
  kvar T : ExpressionType
  kvar S S1 S2 : Statement
  kvar K K1 K2 : K
  kvar KernelC Param : KernelC
  kvar KernelCList ParamList ArgList: List{KernelC}
  kvar Map Env TEnv : Map
  kvar Stack : List
  kvar Set : Set

  syntax K ::= List{KernelC}
  syntax K ::= runMain
  syntax K ::= fieldList ( List{KernelC} )
  syntax TypedValue ::= localRef ( Id )
  syntax TypedValue ::= newObject
  syntax K ::= restoreEnv ( Set )
  syntax ListItem ::= callContext ( K , K , Map , Map )

  /* Function definition/declaration */
  rule
    <k> T:Type F:Id(PDs:ParameterDeclarations) S:Statement => .K ...</k>
    <fun>... .Map => T F(PDs) |-> { S return; } ...</fun>
  [structural]
  /* elide function declarations */
  rule T:Type F:Id(PDs:ParameterDeclarations) => .K  [structural]

  /* Structure declaration */
  rule
    <k> struct X:Id {  } ; => .K ...</k>
    <struct>... .Map => X |-> fieldList(KernelCList) ...</struct>
  [structural]


***(
Variable declaration
***)
  rule
    <k> T X ; => .K ...</k>
    <env>... .Map => X |-> undef ...</env>
    <tenv>... .Map =>  X |-> T ...</tenv>
    <counter> N => sNat N </counter>
  [structural]
 

***(
Statements
***)
  rule _:TypedValue; => .K    [structural]
  rule
    <k>
        {}
      =>
        KernelC ~> restoreEnv(keys(Env) SetItem(id("__return__")))
    ...</k>
    <env> Env </env>
  [structural]
  rule
    <k> restoreEnv(Set) => .K ...</k>
    <env> Env => filterMap(Env, Set) </env>
    <tenv> TEnv => filterMap(TEnv, Set) </tenv>
  [structural]
  rule if(tv(_, NzI)) S1 else S2 => S1 [structural]
  rule if(tv(_, 0)) S1 else S2 => S2 [structural]
  rule
    while (E:Expression) S:Statement => if (E) { S while(E) S }
  [structural]


***(
Function call/return
***)
*** function call
  rule
    <fun>... T F(ParamList) |-> S ...</fun>
    <k>
        _`(_`)(F, ArgList) ~> K
      =>
        declParams(ParamList) ~> bindParams(ParamList, ArgList) ~> S
    </k>
    <stack> .List => callContext(FName, K, TEnv, Env) ...</stack>
    <fname> FName => F </fname>
    <tenv> TEnv => .Map </tenv>
    <env> Env => .Map </env>

*** return
  rule
    <k> return TV ~> _ => TV ~> K </k>
    <stack> callContext(F, K, TEnv, Env) => .List ...</stack>
    <fname> _ => F </fname>
    <tenv> _ => TEnv </tenv>
    <env> _ => Env </env>


***(
Expressions
***)
  /* variable lookup */
  rule
    <k> X => tv(T, V) ...</k>
    <env>... X |-> V ...</env>
  [structural]

*** unary expressions
  rule -tv(T, I) => tv(T, -Int I) [structural]
  rule !TV => TV ? tv(int, 0) : tv(int, 1) [structural]

  /* referencing */
  context &([HOLE]->_)
  rule
    <k>
      &(ObjectPointer(struct S:Id, I:Int)->F:Id)
    =>
      MemberPointer(T, I:Int, F)
    ...</k>
    <struct>...
      S |-> (F |-> T _:Map)
    ...</struct>
  [structural]
  rule
    <k>
      &X:Id => ObjectPointer(T, I:Int)
    </k>
    <env>... X |-> ObjectPointer(T, I:Int) ...</env>
  [structural]

*** dereferencing
  rule
    <k> *tv(T *, I) => derive(I) ~> load(T, I) ...</k>
  [structural]
  rule
    <k> E:Expression->F:Id => *&(E->F) ...</k>
  [structural]
  rule *localRef(X) => X [structural]
  
*** binary expressions
  rule tv(T, I1) + tv(T, I2) => tv(T, I1 +Int I2) [structural]
  rule tv(T *, I1) + tv(int, I2) => tv(T *, I1 +Int I2) [structural]
  rule tv(int, I1) + tv(T *, I2) => tv(T *, I1 +Int I2) [structural]
  rule tv(T, I1) - tv(T, I2) => tv(T, I1 -Int I2) [structural]
  rule tv(T *, I1) - tv(int, I2) => tv(T *, I1 -Int I2) [structural]
  rule tv(T *, I1) - tv(T *, I2) => tv(int, I1 -Int I2) [structural]  
  rule tv(T, I1) * tv(T, I2) => tv(T, I1 *Int I2) [structural]
  rule tv(T, I) / tv(T, NzI) => tv(T, I /Int NzI) [structural]
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
    <k> X = tv(T, V) => tv(T, V) ...</k>
    <env>... X |-> (_ => V) ...</env>
  [structural]
  context (*[HOLE]) = _
  rule
    <k> *tv(T *, I) = tv(_, V) => derive(I) ~> store(T, I, V) ...</k>
  [structural]
  context ([HOLE]->_) = _
  rule
    <k> tv(T, I)->F = E => *&(tv(T, I)->F) = E ...</k>
  [structural]
  rule
    <k> *localRef(X) = tv(T, V) => tv(T, V) ...</k>
    <env>... X |-> (_ => V) ...</env>
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

  /* sizeof */
  rule sizeof(int) => tv(int, 1)        [structural]
  rule
    <k> sizeof(struct X) => tv(int, listLen(KernelCList)) ...</k>
    <struct>... X |-> fieldList(KernelCList) ...</struct>
  [structural]
  rule sizeof(T:Type*) => tv(int, 1)    [structural]


***(
Memory load, store and rearrangement
***)
*** structure fields
  rule
    <k> derive(I) => .K ...</k>
    <heap>... I |-> _ : _ ...</heap>
  [structural]
  rule
    <k> load(T, I) => tv(T, V) ...</k>
    <heap>... I |-> V : _ ...</heap>
  rule
    <k> store(T, I, V) => tv(T, V) ...</k>
    <heap>... I |-> (_ => V) : _ ...</heap>

*** pointers to ints and pointers
  rule
    <k> derive(I) => .K ...</k>
    <heap>... I |-> _ ...</heap>
  [structural]
  rule
    <k> load(T, I) => tv(T, V) ...</k>
    <heap>... I |-> V ...</heap>
  rule
    <k> store(T, I, V) => tv(T, V) ...</k>
    <heap>... I |-> (_ => V) ...</heap>


***(
Memory management
***)
*** malloc/free
  rule id("malloc")(TV) => newObject [structural]
  rule (T *) newObject => new T [structural]
  rule id("free")(TV) => delete TV [structural]

*** new
  rule
    <k> new struct X => tv(struct X *, FreeInt(N)) ...</k>
    <heap>... .Map => initObject(FreeInt(N), X, KernelCList) ...</heap>
    <struct>... X |-> fieldList(KernelCList) ...</struct>
    <counter> N => sNat N </counter>
  rule
    <k> new int => tv(int *, FreeInt(N)) ...</k>
    <heap>... .Map => FreeInt(N) |-> undef ...</heap>
    <counter> N => sNat N </counter>
  rule
    <k> new (T *) => tv(T **, FreeInt(N)) ...</k>
    <heap>... .Map => FreeInt(N) |-> undef ...</heap>
    <counter> N => sNat N </counter>

*** delete
  rule
    <k>
        delete tv(struct X *, I)
      =>
        derive(I) ~> deleteObject(I, listLen(KernelCList))
    ...</k>
    <struct>... X |-> fieldList(KernelCList) ...</struct>
  rule
    <k> delete tv(int *, I) => tv(void, unit) ...</k>
    <heap>... I |-> _ => .Map ...</heap>
  rule
    <k> delete tv(T **, I) => tv(void, unit) ...</k>
    <heap>... I |-> _ => .Map ...</heap>
  rule
    <k> deleteObject(I, (sNat N => N)) ...</k>
    <heap>... I +Int N |-> _ : _ => .Map ...</heap>
  rule
    <k> deleteObject(I, 1) => tv(void, unit) ...</k>
    <heap>... I |-> _ : _ => .Map ...</heap>


***(
I/O
***)
  rule
    <k> read(T) => tv(T, I) ...</k>
    <in> ListItem(I) => .List ...</in>
  [structural]
  rule
    <k>
        id("scanf")(tv(string, _:String),,, localRef(X))
      =>
        (X = read(int)); ~> tv(void, unit)
    ...</k>
  [structural]
  rule
    <k>
        id("scanf")(tv(string, _:String),,, tv(T *, I))
      =>
        (*tv(T *, I) = read(T)); ~> tv(void, unit)
    ...</k>
  [structural]
  rule
    <k> id("printf")(tv(string, _:String),,, tv(_, I)) => tv(void, unit) ...</k>
    <out>... .List => ListItem(I) </out>
  [structural]
  rule id("printf")(tv(string, _:String)) => tv(void, unit) [structural]


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

  syntax Map ::= initObject ( Int++ , Id , List{KernelC} )
  rule
      initObject(I, X , (_ F;),,, KernelCList)
    =>
      I |-> undef : X.F initObject(I +Int 1, X , KernelCList)
  [structural]
  rule initObject(_, _ , .List{KernelC}) => .Map [structural]

  syntax Map ::= filterMap ( Map , Set )
  rule
      filterMap((K1 |-> K2 Map), Set)
    =>
      if SetItem(K1) in Set then K1 |-> K2 else .Map fi
      filterMap(Map, Set)
  [structural]
  rule filterMap(.Map, _) => .Map [structural]
endkm

