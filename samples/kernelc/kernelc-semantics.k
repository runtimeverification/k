module KERNELC-SEMANTICS
  imports KERNELC-SYNTAX

  /*
   * Macros
   */
  rule if (E:Expression) S:Statement => if (E) S else ;   [macro]
  rule E1:Expression || E2:Expression => (E1 ? 1 : E2)    [macro]
  rule E1:Expression && E2:Expression => (E1 ? E2 : 0)    [macro]
  rule !E:Expression => (E ? 0 : !)                       [macro]
  rule return; => return tv(void, undef);                 [macro]


  /*
   * KernelC configuration 
   */
  configuration
    <config> 
      <struct> .Map </struct>
      <fun> .Map </fun>

      <k> $PGM:File ~> main(.Expressions) </k>
      <env> .Map </env>
      <fun-id> .K </fun-id>
      <stack> .List </stack>
               
      <heap> .Map </heap>

      <in> .List </in>
      <out> .List </out>
    </config>


  syntax KResult ::= TypedValue | Bool


  syntax Expression ::= TypedValue | Bool
  syntax TypedValue ::= "tv" "(" Type "," Value ")"
  syntax TypedValues ::= List{TypedValue, ","}
  syntax Value ::= Int
                 | Pointer
                 | "undef"
  syntax Pointer ::= "ObjectPointer" "(" Int ")"
                   | "MemberPointer" "(" Int "," Id ")"
                   | "Null"


  /*
   * Definitions/declarations
   */
  /* Function definition/declaration */
  rule
    <k> T:Type F:Id(PDs:ParameterDeclarations) S:Statement => .K ...</k>
    <fun>... .Map => T F(PDs) |-> { S return; } ...</fun>
    [structural]
  /* elide function declarations */
  rule T:Type F:Id(PDs:ParameterDeclarations); => .K   [structural]

  /* Structure declaration */
  rule
    <k> struct S:Id { VDs:VariableDeclarations }; => .K ...</k>
    <struct>... .Map => X |-> makeMemberMap(VDs) ...</struct>
    [structural]

  /* Variable declaration */
  rule
    <k> T:Type X:Id; => .K ...</k>
    <env> Env:Map => Env[X <- ObjectPointer(!I:Int)] </env>
    <heap>... .Map => ObjectPointer(I) |-> undef ...</heap>
    [structural]
 
  /*
   *
   */
  rule _:TypeValue; => .K   [structural]
  rule ; => .K              [structural]
  rule
    <k> { VDs:VariableDeclarations Ss:Statements } => VDs ~> Ss ~> Env ...</k>
    <env> Env:Map </env>
    [structural]
  rule
    // TODO: delete locals
    //<k> Env:Map => deleteLocals() ...</k>
    <k> Env:Map => .K ...</k>
    <env> OuterEnv:Map => Env </env>
    [structural]


  /*
   * If/choice
   */
  rule if (E:Expression) S1:Statement else S2:Statement
    => expression2bool(E) ~> if (HOLE) S1 else S2
    [heat]
  rule B:Bool ~> if (HOLE) S1:Statement else S2:Statement
    => if (B) S1 else S2
    [cool]
  rule if( true) S:Statement else _:Statement => S    [structural]
  rule if(false) _:Statement else S:Statement => S    [structural]

  rule E1:Expression ? E2:Expression : E3:Expression
    => expression2bool(E1) ~> HOLE ? E2 : E3
    [heat]
  rule B:Bool ~> HOLE ? E1:Expression : E2:Expression
    => B ? E1 : E2
    [cool]
  rule  true ? E:Expression : _:Expression => E   [structural]
  rule false ? _:Expression : E:Expression => E   [structural]

  syntax KItem ::= "expression2bool" "(" Expression ")"           [strict]
  rule expression2bool(tv(int, I:Int)) => I =/=K 0                [structural]
  rule expression2bool(tv(T:Type *, P:Pointer)) => P =/=K Null    [structural]

  /*
   * while
   */
  rule while (E:Expression) S:Statement => if (E) { S while(E) S }
    [structural]


  /*
   * Function call/return
   */
  syntax KItem ::= callStackFrame(K, Map, Id)
  rule
    <fun>... _:Type Callee(PDs:ParameterDeclarations) |-> S:Statement ...</fun>
    <k>
        Callee:Id(TVs:TypedValues) ~> K
      =>
        // TODO(add append on Statements)
        { declareParameters(PDs) { bindParameters(PDs, TVs) } S }
    </k>
    <stack> .List => ListItem(callStackFrame(K, Env, Caller)) ...</stack>
    <fun-id> Caller:Id => Callee </fun-id>
    <env> Env:Map => .Map </env>
  rule
    <fun>... T Callee(_:ParameterDeclarations) |-> _:Statement ...</fun>
    <k> return tv(T:Type, V:Value); ~> _ => tv(T, V) ~> K </k>
    <stack> ListItem(callStackFrame(K, Env:Map, Caller:Id)) => .List ...</stack>
    <fun-id> Callee:Id => Caller </fun-id>
    <env> _:Map => Env </env>


  /*
   * Memory operations
   */
  rule X:Id => *&X                      [structural]
  rule E:Expression->F:Id => *&(E->F)   [structural]
  rule &*E:Expression => E              [structural]

  /* memory address computation */
  rule
    <k> &X:Id => TV </k>
    <env>... X |-> TV:TypedValue ...</env>
    [structural]
  context &(HOLE->_)
  rule
    <k>
      &(tv(struct S:Id *, ObjectPointer(I:Int))->F:Id)
    =>
      tv(T *, MemberPointer(I, F))
    ...</k>
    <struct>... S |-> (F |-> T:Type _:Map) ...</struct>
    [structural]

  /* memory location read */
  rule
    <k> *tv(T:Type *, ObjectPointer(I:Int)) => tv(T, V) ...</k>
    <heap>... ObjectPointer(I) |-> tv(T, V:Value) ...</heap>
    requires V =/=K undef
    [transition]
  rule
    <k> *tv(T:Type *, MemberPointer(I:Int, F:Id)) => tv(T, V) ...</k>
    <heap>... ObjectPointer(I) |-> (F |-> tv(T, V:Value) _:Map) ...</heap>
    requires V =/=K undef
    [transition]

  /* memory location write */
  rule E1:Expression = E2:Expression; => &E1 ~> HOLE = E2;    [heat]
  rule TV:TypedValue ~> HOLE = E:Expression; => TV = E;       [cool]
  rule
    <k> tv(T:Type *, ObjectPointer(I:Int)) = tv(T, V:Value); => .K ...</k>
    <heap>... ObjectPointer(I) |-> tv(T, _:Value => V) ...</heap>
    requires V =/=K undef
    [transition]
  rule
    <k> tv(T:Type *, MemberPointer(I:Int, F:Id)) = tv(T, V:Value); => .K ...</k>
    <heap>... ObjectPointer(I) |-> (F |-> tv(T, _:Value => V) _:Map) ...</heap>
    requires V =/=K undef
    [transition]
  
  /*
   * boolean and arithmetic operations
   */
  rule -tv(int, I:Int) => tv(int, -Int I)   [structural]
  rule ~tv(int, I:Int) => tv(int, ~Int I)   [structural]
  rule
    tv(int, I1:Int) + tv(int, I2:Int) => tv(int, I1 +Int I2)
    [structural]
  rule
    tv(int, I1:Int) - tv(int, I2:Int) => tv(int, I1 -Int I2)
    [structural]
  rule
    tv(int, I1:Int) * tv(int, I2:Int) => tv(int, I1 *Int I2)
    [structural]
  rule
    tv(int, I1:Int) / tv(int, I2:Int) => tv(int, I1 /Int I2)
    requires I2 =/=K 0
    [structural]
  rule
    tv(int, I1:Int) % tv(int, I2:Int) => tv(int, I1 %Int I2)
    requires I2 =/=K 0
    [structural]
  rule
    tv(int, I1:Int) << tv(int, I2:Int) => tv(int, I1 <<Int I2)
    [structural]
  rule
    tv(int, I1:Int) >> tv(int, I2:Int) => tv(int, I1 >>Int I2)
    [structural]
  rule
    tv(int, I1:Int) >= tv(int, I2:Int) => tv(int, bool2int(I1 >=Int I2))
    [structural]
  rule
    tv(int, I1:Int) >  tv(int, I2:Int) => tv(int, bool2int(I1 >Int  I2))
    [structural]
  rule
    tv(int, I1:Int) <= tv(int, I2:Int) => tv(int, bool2int(I1 <=Int I2))
    [structural]
  rule
    tv(int, I1:Int) <  tv(int, I2:Int) => tv(int, bool2int(I1 <Int  I2))
    [structural]

  rule
    tv(T:Type, I1:Int) == tv(T, I2:Int) => tv(int, bool2int(I1 ==K  I2)) 
    [structural]
  rule
    tv(T:Type, I1:Int) != tv(T, I2:Int) => tv(int, bool2int(I1 =/=K I2))
    [structural]


  /*
   * cast
   */
  // TODO: cast is disabled for now
  //rule (T) tv(_, V) => tv(T, V) [structural]


  /*
   * sizeof
   */
  rule sizeof(int) => tv(int, 1)        [structural]
  rule sizeof(T:Type *) => tv(int, 1)   [structural]
  rule
    <k> sizeof(struct S:Id) => tv(int, size(Members)) ...</k>
    <struct>... S |-> Members:Map ...</struct>
    [structural]


  /*
   * Memory management
   */
  // TODO: malloc only allocates one structure
  rule
    <k>
      malloc(tv(int, Size:Int)) ~> (struct S:Id *) HOLE
    =>
      tv(struct S *, ObjectPointer(!I:Int))
    ...</k> 
    <heap>... .Map => ObjectPointer(!I) |-> initializeObject(Members) ...</heap>
    <struct>... S |-> Members:Map ...</struct>
    when Size ==K size(Members)
    [structural]
  rule
    <k> free(tv(T:Type *, ObjectPointer(I:Int))) => tv(void, undef) ...</k>
    <heap>... ObjectPointer(I) |-> _ => .Map ...</heap>


  /*
   * I/O
   */
/*
  rule
    <k> read(T) => tv(T, I) ...</k>
    <in> ListItem(I) => .List ...</in>
  [structural]
  rule
    <k>
        scanf(tv(string, _:String), tv(T:Type * = X))
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
    <k> printf(tv(string, _:String), tv(_:Type, )) => tv(void, unit) ...</k>
    <out>... .List => ListItem(I) </out>
  [structural]
  rule id("printf")(tv(string, _:String)) => tv(void, unit) [structural]
*/


  /*
   * Helper functions
   */
  syntax Map ::= initializeObject(Map)    [function]
  rule initializeObject(F:Id |-> T:Type M:Map)
    => F |-> tv(T, undef) initializeObject(M)
  rule initializeObject(.Map) => .Map

  /*
  syntax Map ::= filterMap ( Map , Set )
  rule
      filterMap((K1 |-> K2 Map), Set)
    =>
      if SetItem(K1) in Set then K1 |-> K2 else .Map fi
      filterMap(Map, Set)
  [structural]
  rule filterMap(.Map, _) => .Map [structural]
  */

  syntax Map ::= makeMemberMap(VariableDeclarations)    [function]
  rule makeMemberMap(T:Type X:Id; VDsVariableDeclarations)
    => X |-> T makeMemberMap(VDs)
  rule makeMemberMap(.VariableDeclarations) => .Map

  syntax VariableDeclarations ::= declareParameters(ParameterDeclarations)
    [function]
  rule declareParameters(T:Type X:Id, PDs:ParameterDeclarations)
    => T X; declareParameters(PDs) 
  rule declareParameters(.ParameterDeclarations) => .VariableDeclarations

  syntax Statements ::= bindParameters(ParameterDeclarations, TypedValues)
    [function]
  rule bindParameters(
          (T:Type X:Id, PDs:ParameterDeclarations),
          (tv(T, V:Value), TVs:TypedValues)) 
    => X = tv(T, V); bindParameters(PDs, TVs)
  rule bindParameters(.ParameterDeclarations, .TypedValues) => .Statements
endmodule

