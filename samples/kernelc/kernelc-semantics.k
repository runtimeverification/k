// Copyright (c) 2014 K Team. All Rights Reserved.

module KERNELC-SEMANTICS
  imports KERNELC-SYNTAX

  /*
   * Macros
   */
  rule return; => return tv(void, undef);                   [macro]
  rule NULL => tv(void *, null)                             [macro]

  /* block without declarations macro (for use in the semantics only) */
  syntax Block ::= "{" Statements "}"
  rule { Ss:Statements } => { .VariableDeclarations Ss }    [macro]


  /*
   * Typed values
   */
  syntax Expression ::= EvaluatedExpression
  syntax EvaluatedExpression ::= TypedValue
                               | Bool
                               | String
  syntax EvaluatedExpressions ::= List{EvaluatedExpression, ","}

  syntax TypedValue ::= "tv" "(" Type "," Value ")"
  syntax Value ::= Int
                 | Pointer
                 | "undef"
  syntax Pointer ::= "object" "(" Int ")"
                   | "member" "(" Int "," Id ")"
                   | "null"


  /*
   * Process global definitions and declarations one at a time
   */
  rule G:Global Gs:Globals => G ~> Gs   [structural]
  rule .Globals => .K                   [structural]


  /*
   * Elide #include directives
   */
  rule #include<stdlib.h> => .K   [structural]
  rule #include<stdio.h>  => .K   [structural]


  /*
   * Definitions/declarations
   */
  /* Function definition */
  syntax KItem ::= functionBody(ParameterDeclarations, Type, Block)
  rule
    <k> T:Type F:Id(PDs:ParameterDeclarations) B:Block => .K ...</k>
    <fun>... .Map => F |-> functionBody(PDs, T, { B return; }) ...</fun>
    [structural]
  /* Elide function declarations */
  rule T:Type F:Id(PDs:ParameterDeclarations); => .K   [structural]

  /* Structure declaration */
  rule
    <k> struct S:Id { VDs:VariableDeclarations }; => .K ...</k>
    <struct>... .Map => S |-> makeMemberMap(VDs) ...</struct>
    [structural]

  /* Variable declaration */
  rule VD:VariableDeclaration VDs:VariableDeclarations => VD ~> VDs
    [structural]
  rule .VariableDeclarations => .K    [structural]
  rule
    <k> T:Type X:Id; => .K ...</k>
    <env> Env:Map => Env[X <- tv(T *, object(!I:Int))] </env>
    <heap>... .Map => object(!I) |-> tv(T, undef) ...</heap>
    [structural]


  /*
   * Structural statements
   */
  rule S:Statement Ss:Statements => S ~> Ss   [structural]
  rule .Statements => .K                      [structural]


  /*
   * Sequence point
   */
  rule _:TypedValue; => .K    [structural]
  rule ; => .K                [structural]


  /*
   * Block statement
   */
  rule
    <k> { VDs:VariableDeclarations Ss:Statements } => VDs ~> Ss ~> Env ...</k>
    <env> Env:Map </env>
    [structural]
  rule
    <k> Env:Map => deleteLocals(values(BlockEnv -Map Env)) ...</k>
    <env> BlockEnv:Map => Env </env>
    [structural]

  syntax KItem ::= deleteLocals(List)
  rule
    <k> deleteLocals((ListItem(tv(_:Type, P:Pointer)) => .List) L:List) ...</k>
    <heap>... P |-> _ => .Map...</heap>
    [structural]
  rule deleteLocals(.List) => .K    [structural]


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
  rule expression2bool(tv(T:Type *, P:Pointer)) => P =/=K null    [structural]


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
    <fun>...
      Callee |-> functionBody(PDs:ParameterDeclarations, _:Type, B:Block)
    ...</fun>
    <k>
        Callee:Id(EEs:EvaluatedExpressions) ~> K
      =>
        { declareParameters(PDs) bindParameters(PDs, EEs, B) }
    </k>
    <stack> .List => ListItem(callStackFrame(K, Env, Caller)) ...</stack>
    <fun-id> Caller:Id => Callee </fun-id>
    <env> Env:Map => .Map </env>
    // TODO: handle special function more generically
    requires Callee =/=K malloc andBool Callee =/=K free
     andBool Callee =/=K scanf andBool Callee =/=K printf
  rule
    <fun>...
      Callee |-> functionBody(_:ParameterDeclarations, T, _:Block)
    ...</fun>
    <k>
      return tv(T:Type, V:Value); ~> _
    =>
      deleteLocals(values(CalleeEnv)) ~> tv(T, V) ~> K
    </k>
    <stack>
      ListItem(callStackFrame(K, CallerEnv:Map, Caller:Id)) => .List
    ...</stack>
    <fun-id> Callee:Id => Caller </fun-id>
    <env> CalleeEnv:Map => CallerEnv </env>


  /*
   * Memory operations
   */
  rule X:Id => *&X                      [structural]
  rule E:Expression->F:Id => *&(E->F)   [structural]
  rule &*E:Expression => E              [structural]

  /* memory address computation */
  rule
    <k> &X:Id => TV ...</k>
    <env>... X |-> TV:TypedValue ...</env>
    [structural]
  context &(HOLE->_)
  rule
    <k>
      &(tv(struct S:Id *, object(I:Int))->F:Id)
    =>
      tv(T *, member(I, F))
    ...</k>
    <struct>... S |-> (F |-> T:Type _:Map) ...</struct>
    [structural]

  /* memory read */
  rule
    <k> *tv(T:Type *, object(I:Int)) => tv(T, V) ...</k>
    <heap>... object(I) |-> tv(T, V:Value) ...</heap>
    requires V =/=K undef
    [transition]
  rule
    <k> *tv(T:Type *, member(I:Int, F:Id)) => tv(T, V) ...</k>
    <heap>... object(I) |-> (F |-> tv(T, V:Value) _:Map) ...</heap>
    requires V =/=K undef
    [transition]

  /* memory write */
  rule E1:Expression = E2:EvaluatedExpression; => &E1 ~> HOLE = E2;   [heat]
  rule TV:TypedValue ~> HOLE = E:EvaluatedExpression; => TV = E;      [cool]
  rule
    <k> tv(T:Type *, object(I:Int)) = tv(T, V:Value); => .K ...</k>
    <heap>... object(I) |-> tv(T, _:Value => V) ...</heap>
    requires V =/=K undef
    [transition]
  rule
    <k> tv(T:Type *, member(I:Int, F:Id)) = tv(T, V:Value); => .K ...</k>
    <heap>... object(I) |-> (F |-> tv(T, _:Value => V) _:Map) ...</heap>
    requires V =/=K undef
    [transition]

  /*
   * Boolean and arithmetic operations
   */
  rule I:Int => tv(int, I)                    [structural]
  // TODO: node unary -Int?
  rule -tv(int, I:Int) => tv(int, 0 -Int I)   [structural]
  rule ~tv(int, I:Int) => tv(int, ~Int I)     [structural]
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
    tv(int, I1:Int) >= tv(int, I2:Int) => bool2int(I1 >=Int I2)
    [structural]
  rule
    tv(int, I1:Int) >  tv(int, I2:Int) => bool2int(I1 >Int  I2)
    [structural]
  rule
    tv(int, I1:Int) <= tv(int, I2:Int) => bool2int(I1 <=Int I2)
    [structural]
  rule
    tv(int, I1:Int) <  tv(int, I2:Int) => bool2int(I1 <Int  I2)
    [structural]

  rule
    tv(T:Type, V1:Value) == tv(T, V2:Value) => bool2int(V1 ==K  V2)
    [structural]
  rule
    tv(T:Type, V1:Value) != tv(T, V2:Value) => bool2int(V1 =/=K V2)
    [structural]

  syntax KItem ::= "bool2int" "(" Bool ")"
  rule bool2int( true) => tv(int, 1)    [structural]
  rule bool2int(false) => tv(int, 0)    [structural]


  /*
   * Cast
   */
  // TODO: cast is disabled for now
  //rule (T) tv(_, V) => tv(T, V) [structural]


  /*
   * Pointer conversions
   */
  rule tv(T1:Type **, _:Pointer) = tv((T2:Type * => T1 *), null);
    requires T1 =/=K T2
    [structural]
  rule tv(T1:Type *, _:Pointer) == tv((T2:Type * => T1 *), null)
    requires T1 =/=K T2
    [structural]
  rule tv((T1:Type * => T2 *), null) == tv(T2:Type *, _:Pointer)
    requires T1 =/=K T2
    [structural]
  rule tv(T1:Type *, _:Pointer) != tv((T2:Type * => T1 *), null)
    requires T1 =/=K T2
    [structural]
  rule tv((T1:Type * => T2 *), null) != tv(T2:Type *, _:Pointer)
    requires T1 =/=K T2
    [structural]
  rule
    <fun>...
      Callee |-> functionBody(_:ParameterDeclarations, T2:Type *, _:Block)
    ...</fun>
    <k> return tv((T1:Type * => T2 *), null); ...</k>
    <fun-id> Callee:Id </fun-id>
    [structural]


  /*
   * Sizeof
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
  /* malloc only allocates one structure */
  // TODO: check why the HOLE below does not become a freezer
  rule
    <k>
      malloc(tv(int, Size:Int)) ~> (struct S:Id *) HOLE:>Expression
    =>
      tv(struct S *, object(!I:Int))
    ...</k>
    <heap>... .Map => object(!I) |-> initializeObject(Members) ...</heap>
    <struct>... S |-> Members:Map ...</struct>
    when Size ==K size(Members)
    [structural]
  syntax TypedValue ::= makeNewObject(Int)
  rule malloc(tv(int, Size:Int)) => makeNewObject(Size)
  rule
    <k>
      (struct S:Id *) makeNewObject(Size)
    =>
      tv(struct S *, object(!I:Int))
    ...</k>
    <heap>... .Map => object(!I) |-> initializeObject(Members) ...</heap>
    <struct>... S |-> Members:Map ...</struct>
    when Size ==K size(Members)
    [structural]
  rule
    <k> free(tv(T:Type *, object(I:Int))) => tv(void, undef) ...</k>
    <heap>... object(I) |-> _ => .Map ...</heap>


  /*
   * I/O
   */
  rule
    <k>
      scanf(_:String, tv(int *, P:Pointer))
    =>
      tv(int *, P) = tv(int, I); ~> tv(void, undef)
    ...</k>
    <in> ListItem(I:Int) => .List ...</in>
    [structural]
  rule
    <k> printf(_:String, tv(int, I:Int)) => tv(void, undef) ...</k>
    <out>... .List => ListItem(I) </out>
    [structural]
  rule printf(_:String) => tv(void, undef)   [structural]


  /*
   * Helper functions
   */
  syntax Map ::= initializeObject(Map)    [function]
  rule initializeObject(F:Id |-> T:Type M:Map)
    => F |-> tv(T, undef) initializeObject(M)
  rule initializeObject(.Map) => .Map

  syntax Map ::= makeMemberMap(VariableDeclarations)    [function]
  rule makeMemberMap(T:Type X:Id; VDs:VariableDeclarations)
    => X |-> T makeMemberMap(VDs)
  rule makeMemberMap(.VariableDeclarations) => .Map

  syntax VariableDeclarations ::= declareParameters(ParameterDeclarations)
    [function]
  rule declareParameters(T:Type X:Id, PDs:ParameterDeclarations)
    => T X; declareParameters(PDs)
  rule declareParameters(.ParameterDeclarations) => .VariableDeclarations

  syntax Statements ::=
    bindParameters(ParameterDeclarations, EvaluatedExpressions, Block)
    [function]
  rule bindParameters(
          (_:Type X:Id, PDs:ParameterDeclarations),
          (TV:TypedValue, EEs:EvaluatedExpressions),
          B:Block)
    => X = TV; bindParameters(PDs, EEs, B)
  rule bindParameters(.ParameterDeclarations, .EvaluatedExpressions, B:Block)
    => B
endmodule

