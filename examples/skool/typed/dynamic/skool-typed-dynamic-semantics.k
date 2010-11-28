--------------------------------------------
--- SKOOL-TYPED-DYNAMIC-SEMANTICS module ---
--------------------------------------------

kmod SKOOL-TYPED-DYNAMIC-SEMANTICS is including SKOOL-TYPED-DYNAMIC-DESUGARED-SYNTAX + K 

-------------------------------------------------------------
--- Values that various fragments of programs evaluate to ---
-------------------------------------------------------------

  syntax Val ::= Int | Bool  
               --- Array values are wrapped as specific reference values, where:
               --- 1st argument = the type of the array
               --- 2nd argument = the location of the first element in the array, and
               --- 3rd argument = the array size (array elements are contiguously allocated)
               | array ( Type , Nat , Nat ) 
               --- Function values; like arrays, functions also evaluate to their address
               --- (wrapped as a specific "function" value together with the function type
               --- and the object that the function corresponds to)
               --- and the address contains the actual function body (as an untyped "lambda" value")
               | function ( Type , K , Nat )
               | lambda ( List{Id} , Stmt ) [latex "\lambda{#1}.{#2}"]
               --- Object values
               | obj ( Id , Nat ) [latex "objEnv({#1},{#2})"]
               | objEnv ( Bag ) [latex "{#1}"]

--- Values are expressions
  syntax Exp ::= Val 


-------------------------------------
--- Computations "swallow" syntax ---
-------------------------------------

--- We have to subsort all the syntactic categories to K, and the lists of values
--- to KResult.  Recall that the second argument of a method application is a list
--- of expressions, so that becomes a result when it becomes a list of values
  syntax K ::= Stmts | List{Exp} | List{Type} | List{VarType} | List{Top}
  syntax KResult ::= List{Val} 


---------------------
--- Configuration ---
---------------------

  configuration <T> 
                    <k> K:K </k>
                    <fstack> .List </fstack>
                    <env> .Map </env>
                    <store> .Map </store>
                    <in> .List </in>
                    <out> .List </out>
                    <return> none </return>
                    <nextLoc> 1 </nextLoc>
                    <crntObj> .K </crntObj>
                    <classes>
                        <class*>
                            <className> Id:Id </className>
                            <extends> Id:Id </extends>
                            <declarations> .K </declarations>
                        </class*>
                    </classes>
                </T>

--- Next rule cleans up the configuration at the end, keeping only the output
  rule [terminate]: <T> ((<k>_:Val</k> _) => .) <out>_:List</out> </T>


---------------------------------------
--- Declarations and initialization ---
---------------------------------------

--- Variable declaration
  rule [decl-variable]:
       <k> var X : Tp; => . <_/k>
       <env> Env:Map => Env[L/X] </env>
       <store_> . => L|->initVal(Tp) <_/store>
       <nextLoc> L:Nat => sNat(L) </nextLoc>

--- Array declaration
  context var X:Id[[HOLE]] : T ;
  rule [decl-array]:
       <k> var X[N:Nat] : T[]; => . <_/k> 
       <env> Env => Env[L/X] </env>
       <store_>. => L |-> array(T, sNat L, N) sNat(L)..sNat(L)+Nat N |-> initVal(T) <_/store>
       <nextLoc> L => sNat L +Nat N </nextLoc> 

--- Method declaration
  rule [decl-method]:
       <k> method F:Id(XTl:List{VarType}) : Tp S:Stmt => . <_/k>
       <env> Env => Env[L/F] </env>
       <nextLoc> L => L +Nat 2 </nextLoc>
       <crntObj> Obj:K </crntObj>
       <store_>(. => L|->function(typeList(XTl)->Tp,Obj,sNat(L))  sNat(L)|->lambda(idList(XTl),S))<_/store>

--- Class declaration
  rule [decl-class]:
       <k> class C1:Id extends C2:Id { Ss:Stmts } => . <_/k>
       <classes_> (. => <class_>
                            <className> C1 </className>          
                            <extends> C2 </extends>
                            <declarations> Ss </declarations>
                        <_/class>)
       <_/classes>

--- When we are done with the first pass (preprocessing), i.e., the computation
--- and env are empty (no global environment allowed), create a main object
  rule [call-main]:
       <k> . => new main() </k>
       <env> .Map </env>


-------------------
--- Expressions ---
-------------------

--- Local variable lookup
  rule [lookup-var]:
       <k> X:Id => V:Val <_/k>
       <env_> X |-> L:Nat <_/env>
       <store_> L |-> V <_/store>

--- Field lookup.  If X is not in the local environment, then assume that
--- it's a field of "this".  General object lookup defined as auxilliary below
  rule [lookup-field]:
       <k> X => _._(this,X) <_/k>   --- to avoid parsing ambiguity, use _._(this,X) instead of this.X
       <env> Env:Map </env>
    if notBool(X in keys(Env)) [structural]




  rule [this]:
       <k> this => Obj <_/k>  
       <crntObj> Obj </crntObj>

  rule [super]:
       <k> _._((super => obj(C',L)),X) <_/k>
       <crntObj> obj(C,L) </crntObj>
       <className> C </className> 
       <extends> C' </extends>

  syntax K ::= lookupF ( Bag , Id )

  context ('_._(`[HOLE`]:K,,_)) if (`[HOLE`]:K =/=Bool super)

  --- looking up in object
  syntax CellLabel ::= envStack 

  rule <k> _._(obj(C,L),X) => lookupF(<envStack>  (C :: EnvC:Bag) EStack:List </envStack>, X) <_/k>
      <store_> L |-> objEnv(<envStack_> (C :: EnvC) EStack </envStack>) <_/store>

  --- lookup using object environment
  rule lookupF(<envStack> _ :: <env_>  X |-> L:Nat <_/env> <_/envStack>,X) => lookup(L)

  --- recursing through the object environment stack
  rule lookupF(<envStack> _ :: <env> Env </env>  => . <_/envStack>, X)
       if notBool(X in keys(Env)) [structural]




--- Variable/Field/Array Increment
--- This is tricky, because we want to allow all of ++x, ++o.x, ++a[5]
--- Therefore, we need to extract the l-value of the expression to increment
--- To do that, we first introduce new syntax for l-values and location values:
  syntax Exp ::= l-value ( K )
  syntax Val ::= loc ( Nat )
--- Then, we state that the expression to increment should be wrapped
--- by l-value and then evaluated.  The semantics of l-value is defined below
  context ++([HOLE] => l-value([HOLE]))
--- l-value eventually produces a location value:
  rule [increment]:
       <k> ++loc(L) => I:Int +Int 1 <_/k>
       <store_> L |-> (I => I +Int 1) <_/store> 

--- Arithmetic operators
  rule I1:Int + I2:Int => I1 +Int I2
  rule _-_(I1,I2) => _-Int_(I1,I2)
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2 if I2 =/=Bool 0
  rule I1 % I2 => I1 %Int I2 if I2 =/=Bool 0
  rule - I => -Int I
  rule I1 < I2 => I1 <Int I2
  rule I1 <= I2 => I1 <=Int I2
  rule I1 > I2 => I1 >Int I2
  rule I1 >= I2 => I1 >=Int I2
  rule V1:Val == V2:Val => V1 ==Bool V2
  rule V1 != V2 => V1 =/=Bool V2
  rule B1:Bool and B2:Bool => B1 andBool B2
  rule B1 or B2 => B1 orBool B2
  rule not(B:Bool) => notBool(B)

--- Array lookup.  Note that we check the array bounds now
--- We prefer to use an auxiliary operation, lookup, to avoid locking the store
  rule [array-indexing]: array(_,L,M:Nat)[N] => lookup(L +Int N)
    if N >=Nat 0 andBool N <=Nat M [structural]

--- Size of array
  rule sizeOf(array(_,_,N)) => N

--- Method call.  SKOOL has dynamic method dispatch, like most OO languages
--- There are several cases to treat, though

--- Case 1: method is called directly, not through an object or super
--- Then "this" is assumed
  rule <k> _`(_`)((X => _._(this,X)),_) <_/k>
--- We would like to write the rule above as
---   rule <k> (X => _._(this,X))(_) <_/k>
--- or even
---   rule <k> (X => this.X)(_) <_/k>
--- but, unfortunately, our current Maude-based parser does not allow it
--- Same applies to the other rules below

--- Case 2: method is called through an object or super
--- There are two subcases

--- Case 2.1: called through a proper object (not super), so dynamic dispatch
--- Then evaluate the object espression and lookup method from top of its environment
  context '_`(_`)('_._(`[HOLE`]:K,,_),,_) if `[HOLE`]:K =/=Bool super 
  rule <k> '_`(_`)(('_._(obj(_,L),,X) => lookupF(Envs:Bag, X)),,_) <_/k>
       <store_> L |-> objEnv(Envs) <_/store>

--- Case 2.2: called through super, so static dispatch from parent class
  rule <k> '_`(_`)(('_._(super,,X) => lookupF(<envStack> EStack </envStack>, X)),,_) <_/k>
       <crntObj> obj(C,L) </crntObj>
       <store_> L |-> objEnv(<envStack_>  (C :: EnvC:Bag) EStack:List </envStack>) <_/store>

--- Eventually, each of the rules above produces a lookup(L) instead of the method
--- When that happens, just lookup the function value at location L
  rule <k> '_`(_`)((lookup(L) => V),,_) <_/k>
       <store_> L |-> V <_/store>

--- Once the function value is retrieved, the next rule applies the actuall call
--- The environment and the computation are pushed onto the stack, etc.
 rule <k> _`(_`)(function(Tpl:List{Type}->Tp,Obj,L),Vl:List{Val}) ~> K => S ~> return(initVal(Tp)); </k>
       <fstack> . => Env # K # Obj' # Tp' <_/fstack>
       <crntObj> Obj':K => Obj </crntObj>
       <env> Env =>  getList{K}(Xl) |-> N..N+Nat|Xl| </env>
       <return> Tp':Type => Tp </return>
       <store_> L|->lambda(Xl:List{Id},S) (. => N..N+Nat|Xl| |-> getList{K}(castAll(Tpl,Vl))) <_/store>
       <nextLoc> N => N +Nat |Xl| </nextLoc>
       <classes> Cls </classes>
    if subtypeAll(typeOfAll(Vl), Tpl, Cls)

--- Function return.  We define it here because it is related to the above
  rule <k> return(V); ~> _ => cast(Tp, V) ~> K </k>
       <fstack> Env # K # Obj # Tp' => . <_/fstack>
       <crntObj> _ => Obj </crntObj>
       <env> _ => Env </env>
       <return> Tp => Tp' </return>
       <classes> Cls </classes>
    if subtype(typeOf(V), Tp, Cls)

--- Read
  rule [input]:
       <k> read() => I <_/k> <in> (ListItem(I) => .) <_/in>

--- New
---   the semantics of the new operator consists of two actions: memory allocation for the new object
---   and the execution of the statements included in the constructor
---   the current class, environment and object are stored on the stack

  rule [new-object]: <k> new C(Vl) ~> K => create(C) ~> _`(_`)(C,Vl); return this; </k>
       <env> Env => . </env>
       <crntObj> Obj => obj(object,L) </crntObj>
       <return> T => C </return>
       <nextLoc> L => sNat L </nextLoc>
       <store_> . => L |-> objEnv(<envStack> object::<env>.Map</env> </envStack>) <_/store>
       <fstack> . => Env # K # Obj # T <_/fstack>


--- create a new object (memory allocation)
---   usually, an object is an instance of a class from an hierarchy
---   a memory object representation is a layered structure: for each class lying on the path 
---   from the current class to the root of the hierarchy there is a layer including the memory
---   allocation for the variable members of that class
  rule [object-allocate]: <k> create(C) => create(C1) ~> setCrntClass(C) ~> Ss ~> addEnvLayer <_/k>
       <classes_>
            <class_>
                   <className> C </className>
                   <extends> C1 </extends>
                   <declarations> Ss:Stmts </declarations>
            <_/class>
       <_/classes>
  rule <k> create(object) => . <_/k>

--- add a new tagged environment layer to the  current object
  rule <k> addEnvLayer => . <_/k>
       <env> Env => . </env>
       <crntObj> obj(C,L) </crntObj>
       <store_> L |-> objEnv(<envStack> . => (C::<env>Env</env>)<_/envStack>)
       <_/store>

  rule <k> setCrntClass(C) => . <_/k>
       <crntObj> obj((_ => C),_) </crntObj>


--- instanceOf operator

  rule [instanceOf]: <k> _instanceOf_(obj(_,L), C1) => subtype(C2,C1,Cls) <_/k>
       <store_> L |-> objEnv(<envStack> C2::_ <_/envStack>) <_/store>
       <classes> Cls:Bag </classes>

  rule [as]: <k> _as_(obj(_,L),C1) => obj(C1,L) <_/k>
             <store_> L |-> objEnv(<envStack> C2::_ <_/envStack>) <_/store>
             <classes>Cls</classes>
        if subtype(C2, C1, Cls)







------------------------------
--- instruction processing ---
------------------------------
  rule {} => .
  rule <k> {Ss:Stmts} => Ss~>env(Env) <_/k> <env> Env:Map </env> 
  rule S1:Stmt S2:Stmt => S1~>S2 

---<SKOOL modified> 
  context ([HOLE] => l-value([HOLE]))=_;

  rule <k> l-value(X) => loc(L) <_/k> <env_> X|->L <_/env> 
  rule <k> l-value(lookup(L)) => loc(L) <_/k>

  rule <k> loc(L)=V1; => . <_/k> <store_> L|->(V2=>cast(typeOf(V2),V1)) <_/store>
       <classes> Cls </classes>
    if subtype(typeOf(V1), typeOf(V2),Cls)

  rule <k> l-value(X => _._(this,X)) <_/k> <env> Env </env> if notBool(X in keys(Env))
  
  context l-value(_._([HOLE],_))

 ---similar lookup as for variables
  rule <k> l-value(_._(obj(C,L), X)  => lookupF(<envStack>  (C :: EnvC) EStack:List </envStack>, X)) <_/k>
       <store_> L |-> objEnv(<envStack_> (C :: EnvC) EStack </envStack>) <_/store>
 
  syntax List{Val} ::= castAll ( List{Type} , List{Val} )
  macro castAll((Tp,Tpl),(V,Vl))
      = cast(Tp,V), castAll(Tpl, Vl)
  macro castAll(.List{Bottom},.List{Bottom}) = .List{Bottom}
  syntax Val ::= cast( Type , Val )
  macro cast(C, obj(_,L)) = obj(C,L) 
  macro cast(T, V2) = V2 [owise]

---</SKOOL modified>

---<SKOOL typed modified>
 --- for array assignment, first evaluate the array and its index
  context l-value(_[[HOLE]])
  context l-value([HOLE][_])
---</SKOOL type modified>
  rule V; => .
  rule if true then S:Stmt else _ => S:Stmt
  rule if false then _ else S => S
  rule <k> while E:Exp do S  => if E then {S while E do S} else {} <_/k>
  rule <k> write(Vl); => . <_/k> <out_> . => List(getList{K}(Vl)) </out>


----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------

  syntax K ::= lookup Nat
  rule [lookup-loc]:
       <k> lookup L => V <_/k> <store_> L |-> V <_/store>

  syntax Val ::=
                 initVal ( Type )
               | none 
  macro initVal(int) = 0 
  macro initVal(bool) = false 
  macro initVal(void) = none 
  macro initVal(_`[`](T:Type)) = array(_`[`](T),0,0) 
  macro initVal(C:Id) = obj(C,0)

  syntax List{Type} ::= typeOfAll ( List{Val} )
  macro typeOfAll(V:Val,Vl:List{Val}) = typeOf(V),typeOfAll(Vl) 
  macro typeOfAll(.List{Bottom}) = .List{Bottom} 
  syntax Type ::= typeOf ( Val )

  macro typeOf(function`(_`,_`,_`)(T,_,_)) = T 
  macro typeOf(array(T,_,_)) = T
  macro typeOf(I:Int) = int 
  macro typeOf(B:Bool) = bool 
  macro typeOf(none) = void 
---<SKOOL added>
  macro typeOf(obj(C,_)) = C
  macro typeOf(objEnv(<envStack> C :: _ <_/envStack>)) = C
---</SKOOL added>
  syntax List{Id} ::= idList ( List{VarType} ) 
  macro idList(.List{Bottom}) = .List{Bottom} 
  macro idList(X:Id : T:Type, XTl:List{VarType}) = X, idList(XTl) 

--- translation of a lists of typed names into a list of the corresponding types
  syntax List{Type} ::= typeList ( List{VarType} ) 
  macro typeList(.List{Bottom}) = .List{Bottom} 
  macro typeList(X : T,XTl) = T,typeList(XTl) 

--- List{Val}
  syntax List{Val} ::= Val | List{Bottom} |  List{Val} , List{Val} [ditto]
  syntax List{Exp} ::= List{Val}

--- length
  syntax Nat ::= `| List{Id} `|
  macro |.List{Bottom}| = 0  
  macro |X:Id, Xl:List{Id}| = sNat |Xl|

--- generate sequence of locations
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..N2:Nat => N1,,sNat N1..N2 [structural]

--- environment recovery
  syntax K ::= env ( Map ) 
  rule env(_) ~> env(Env:Map) => env(Env) [structural] 
  rule <k> env(Env) => . <_/k> <env> _ => Env </env> [structural] 
  rule <k> V:Val ~> (env(Env) => .) <_/k> <env> _ => Env </env> [structural]

---<SKOOL added>

--- an object evironment layer is a map from the class name to the environm. corresp. to local fields
  syntax ListItem ::= Id :: Bag [metadata "latex(renameTo _\\ensuremath{\\mathrel{::}}_)"]
--- the following is nedeed for stacking
  syntax ListItem ::=    Map # K # K # Type 
--- the following are needed at the creation of a new object and at a method call
  syntax K ::= restore ( K ) | discard |  addEnvLayer 
  syntax KLabel ::= create | setCrntClass
--- the names for the local environment and the global environments for an object

--- subtype relationship

  syntax Bool ::= subtypeAll ( List{Type} , List{Type} , Bag ) 
  macro subtypeAll((Tp:Type,Tpl:List{Type}),(Tp':Type,Tpl':List{Type}), Cls) = subtype(Tp,Tp', Cls) andBool subtypeAll(Tpl, Tpl', Cls)
  macro subtypeAll(.List{Bottom},.List{Bottom},_) = true 
  syntax Bool ::= subtype ( Type , Type , Bag ) 
  macro subtype(Tp, Tp, _) = true
  macro subtype(object, C, _) = C ==Bool object
  rule subtype((C1 => C2), C':Id, (Cls <class_> <className> C1 </className> <extends> C2 </extends> </class>)) 
      [structural]
  macro subtype(int, C2,_) = false 
  macro subtype(bool, C2,_) = false 
  macro subtype(void, C2,_) = false 
  macro subtype(C, int,_) = false 
  macro subtype(C, bool,_) = false 
  macro subtype(C, void,_) = false 

---</SKOOL added>


endkm


