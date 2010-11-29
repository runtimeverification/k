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
               --- and the object that the function corresponds to) and the address
               --- contains the actual function body (as an untyped "lambda" value")
               | function ( Type , K , Nat )
               | lambda ( List{Id} , Stmt ) [latex "\lambda{#1}.{#2}"]
               --- Object values
               | obj ( Id , Nat ) --- [latex "objEnv({#1},{#2})"]
               | objEnv ( Bag )   --- [latex "{#1}"]

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
       <k> var X : T; => . <_/k>
       <env> Env:Map => Env[L/X] </env>
       <store_> . => L |-> initVal(T) <_/store>
       <nextLoc> L:Nat => sNat(L) </nextLoc>

--- Array declaration
  context var X[[HOLE]] : T ;
  rule [decl-array]:
       <k> var X[N:Nat] : T[]; => . <_/k> 
       <env> Env => Env[L/X] </env>
       <store_>. => L |-> array(T,sNat(L),N)  sNat(L)..sNat(L) +Nat N |-> initVal(T) <_/store>
       <nextLoc> L => sNat L +Nat N </nextLoc> 

--- Method declaration
--- Like in SIMPLE, method names are added to the environment and bound to their code
--- This way, we can easily allow objects to pass and change their methods (see p23)
  rule [decl-method]:
       <k> method F:Id(XTl) : T S:Stmt => . <_/k>
       <env> Env => Env[L/F] </env>
       <nextLoc> L => L +Nat 2 </nextLoc>
       <crntObj> Obj:K </crntObj>
       <store_>(. => L |-> function(typeList(XTl)->T,Obj,sNat(L))  sNat(L) |-> lambda(idList(XTl),S))<_/store>

--- Class declaration
  rule [decl-class]:
       <k> class C1:Id extends C2:Id { Ss:Stmts } => . <_/k>
       <classes_> (. => <class>
                            <className> C1 </className>
                            <extends> C2 </extends>
                            <declarations> Ss </declarations>
                        </class>)
       <_/classes>

--- When we are done with the first pass (preprocessing), i.e., the computation
--- and env are empty (no global environment allowed), create a main object
  rule [call-main]:
       <k> . => new main() </k>
       <env> . </env>


-------------------
--- Expressions ---
-------------------

--- Local variable lookup
--- If X is in the local environment, then it is a local variable, not a field.
  rule [lookup-var]:
       <k> X => V:Val <_/k>
       <env_> X |-> L:Nat <_/env>
       <store_> L |-> V <_/store>

--- Field lookup
--- If X is not in the local environment, then assume that it's a field of "this".
--- General object lookup defined at its place below (we follow the order in the SKOOL syntax).
  rule [lookup-field]:
       <k> X => _._(this,X) <_/k>   --- to avoid parsing ambiguity, use _._(this,X) instead of this.X
       <env> Env </env>
    if notBool(X in keys(Env)) [structural]

--- Variable/Field/Array Increment
--- This is tricky, because we want to allow all of ++x, ++o.x, ++a[5]
--- Therefore, we need to extract the l-value of the expression to increment.
--- To do that, we state that the expression to increment should be wrapped
--- by the auxilliary "l-value" operation and then evaluated.
--- The semantics of the auxilliary l-value operation is defined below.
--- For now, all we need to know is that it takes an expression and evaluates
--- to a location value, also introduced below with the auxilliary operations.
  context ++([HOLE] => l-value([HOLE]))
--- l-value eventually produces a location value:
  rule [increment]:
       <k> ++loc(L) => I +Int 1 <_/k>
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

--- Array lookup.  Note that we check the array bounds now.
--- We prefer to use an auxiliary operation, lookup (defined in
--- the auxilliary operator section below), to avoid locking the store.
  rule [array-indexing]: array(_,L,M:Nat)[N] => lookup(L +Int N)
    if N >=Nat 0 andBool N <=Nat M [structural]

--- Size of array
  rule sizeOf(array(_,_,N)) => N

--- Method call
---------------
--- SKOOL has dynamic method dispatch, like most OO languages
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
  rule <k> '_`(_`)(('_._(obj(_,L),,X) => lookupMember(Envs:Bag, X)),,_) <_/k>
       <store_> L |-> objEnv(Envs) <_/store>

--- Case 2.2: called through super, so static dispatch from parent class
  rule <k> '_`(_`)(('_._(super,,X) => lookupMember(<envStack> EStack </envStack>, X)),,_) <_/k>
       <crntObj> obj(C,L) </crntObj>
       <store_> L |-> objEnv(<envStack_>  (C :: EnvC) EStack </envStack>) <_/store>

--- Eventually, each of the rules above produces a lookup(L) instead of the method
--- When that happens, just lookup the function value at location L
  rule <k> '_`(_`)((lookup(L) => V),,_) <_/k>
       <store_> L |-> V <_/store>

--- Once the function value is retrieved, the next rule applies the actuall call
--- The environment and the computation are pushed onto the stack, etc.
 rule <k> _`(_`)(function(Tl:List{Type}->T,Obj,L),Vl:List{Val}) ~> K => S ~> return(initVal(T)); </k>
       <fstack> . => Env # K # Obj' # T' <_/fstack>
       <crntObj> Obj':K => Obj </crntObj>
       <env> Env =>  getList{K}(Xl) |-> N..N+Nat|Xl| </env>
       <return> T':Type => T </return>
       <store_> L|->lambda(Xl:List{Id},S) (. => N..N+Nat|Xl| |-> getList{K}(castAll(Tl,Vl))) <_/store>
       <nextLoc> N => N +Nat |Xl| </nextLoc>
       <classes> Cls </classes>
    if subtypeAll(typeOfAll(Vl), Tl, Cls)

--- Function return.  We define it here because it is related to the above
  rule <k> return(V); ~> _ => cast(T, V) ~> K </k>
       <fstack> Env # K # Obj # T' => . <_/fstack>
       <crntObj> _ => Obj </crntObj>
       <env> _ => Env </env>
       <return> T => T' </return>
       <classes> Cls </classes>
    if subtype(typeOf(V), T, Cls)

--- Read
  rule [input]:
       <k> read() => I <_/k> <in> (ListItem(I) => .) <_/in>

--- New
-------
--- The semantics of new consists of two actions: memory allocation for
--- the new object and the execution of the corresponding constructor

--- The current environment and object are stored on the stack and
--- recovered after new, because new destroys them
  rule [initiate-new]:
       <k> new C(Vl) ~> K => create(C) ~> _`(_`)(C,Vl); return this; </k>
       <env> Env => . </env>
       <crntObj> Obj => obj(object,L) </crntObj>
       <return> T => C </return>
       <nextLoc> L => sNat L </nextLoc>
       <store_> . => L |-> objEnv(<envStack> object::<env>.Map</env> </envStack>) <_/store>
       <fstack> . => Env # K # Obj # T <_/fstack>

--- Create a new object (memory allocation)
--- An object is an instance of a class, which can be anywhere in the class hierarchy.
--- A memory object representation is a layered structure: for each class on the path
--- from the instance class to the root of the hierarchy there is a layer including
--- the memory allocated for the members (both fields and methods) of that class.
  rule [object-creation]:
       <k> create(C) => create(C1) ~> setCrntClass(C) ~> Ss ~> addEnvLayer <_/k>
       <className> C </className>
       <extends> C1 </extends>
       <declarations> Ss </declarations>
  rule <k> create(object) => . <_/k>
--- Add a new tagged environment layer to the current object.
--- This is an auxilliary operation, but is used only here.
  rule [add-object-layer]:
       <k> addEnvLayer => . <_/k>
       <env> Env => . </env>
       <crntObj> obj(C,L) </crntObj>
       <store_> L |-> objEnv(<envStack> . => (C::<env>Env</env>)<_/envStack>) <_/store>
--- Set the current class of the current object.
--- This is necessary to be done at each layer, because the current object is enclosed
--- as part of the function values (see the semantics of method declarations above).
--- This is an auxilliary operation, but is used only here.
  rule [set-current-class]:
       <k> setCrntClass(C) => . <_/k>
       <crntObj> obj((_ => C),_) </crntObj>

--- Self reference via "this"
  rule [this]:
       <k> this => Obj <_/k>  
       <crntObj> Obj </crntObj>

--- Object member access
------------------------
--- There are two cases, like for method dispatch

--- Case 1: member access through a proper object (not super)
--- Then evaluate the object expression and lookup member starting with current class (static scoping)
  context ('_._(`[HOLE`]:K,,_)) if (`[HOLE`]:K =/=Bool super)
  rule <k> _._(obj(C,L),X) => lookupMember(<envStack>  (C :: EnvC) EStack </envStack>, X) <_/k>
       <store_> L |-> objEnv(<envStack_> (C :: EnvC) EStack </envStack>) <_/store>

--- Case 2: member access through super
  rule [super]:
       <k> _._((super => obj(C',L)),X) <_/k>
       <crntObj> obj(C,L) </crntObj>
       <className> C </className>
       <extends> C' </extends>

--- instanceOf
  rule [instanceOf]: <k> _instanceOf_(obj(_,L), C1) => subtype(C2,C1,Cls) <_/k>
       <store_> L |-> objEnv(<envStack> C2::_ <_/envStack>) <_/store>
       <classes> Cls:Bag </classes>

--- Casting
  rule [as]: <k> _as_(obj(_,L),C1) => obj(C1,L) <_/k>
             <store_> L |-> objEnv(<envStack> C2::_ <_/envStack>) <_/store>
             <classes>Cls</classes>
        if subtype(C2, C1, Cls)


------------------
--- Statements ---
------------------

--- Empty blocks. One can make the rule below structural, if one doesn't want it to count as step
  rule {} => .

--- Nonempty Blocks. Make sure the environment is recovered after the block executes
--- This rule can also be structural if one does not want entering a block to count as step
  rule <k> {Ss:Stmts} => Ss ~> env(Env) <_/k> <env> Env:Map </env> 

--- Assignment
--- Like for increment, we first compute the l-value of the left-hand-side.
--- Then we cast the assigned value to the type at that l-value
--- (i.e., the type of the value stored there, because we do not change the types of store cells).
  context ([HOLE] => l-value([HOLE]))=_;
  rule [assignment]:
       <k> loc(L)=V1; => . <_/k>
       <store_> L |-> (V2 => cast(typeOf(V2),V1)) <_/store>
       <classes> Cls </classes>
    if subtype(typeOf(V1), typeOf(V2),Cls)

--- Expression statement
  rule [exp-statement]: V; => .

--- Conditional
  rule [if-true]:  if true  then S else _ => S
  rule [if-false]: if false then _ else S => S

--- While
  rule [while]: <k> while E:Exp do S  => if E then {S while E do S} else {} <_/k>

--- Write
  rule [write]: <k> write(Vl); => . <_/k> <out_> . => List(getList{K}(Vl)) </out>

--- Sequential composition.  Desugared into K's sequentialization.  Can also be structural
  rule S1:Stmt S2:Stmt => S1~>S2 


----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------

--- The following operations, listed in the order of their appearence,
--- have been used in the semantics of SKOOL above:
---  - initVal
---  - typeList
---  - idList
---  - l-value
---  - loc
---  - lookup
---  - lookupMember
---  - envStack
---  - _#_#_#_
---  - castAll
---  - subtypeAll
---  - typeOfAll
---  - subtype
---  - typeOf
---  - cast
--- We next declare, define and discuss them in the order of their appearence.
--- In order to define some of them, we need to introduce further auxilliary operations.
--- We also take the opportunity here to define the syntactic categories (or sorts)
--- of all the variables used in this module.

--- initVal
--- This operation associates a default value to each type.
--- Default values are needed in order to give semantics to methods
--- which do not explicitly return a value.  Note that this operation
--- is only a user convenience; the alternative would be require an
--- explicit return statement in each method.  A new "none" value is
--- also included, as a default value of void type.
  syntax Val ::= initVal ( Type ) | none
  macro initVal(int) = 0 
  macro initVal(bool) = false 
  macro initVal(void) = none 
  macro initVal(T:Type[]) = array(T[],0,0) --- array of type T[] of length 0 allocated at location 0
  macro initVal(C:Id) = obj(C,0)           --- object of class C allocated at location 0
--- Note that the first allocated location is 1, so the default arrays/values cannot be accessed

--- idList and typeList
--- Extract the lists of identifiers and of types, respectively, from a list of typed variables.
--- These are used to process the parameters of method declarations, so the typed variables
--- are expected to be typed indentifiers.  If that is not the case, then these operations get stuck.
  syntax List{Id}   ::= idList   ( List{VarType} ) 
  syntax List{Type} ::= typeList ( List{VarType} ) 
  rule idList(.List{Bottom}) => .List{Bottom}                [structural]
  rule idList(X:Id : T, XTl:List{VarType}) => X, idList(XTl) [structural]
  rule typeList(.List{Bottom}) => .List{Bottom}              [structural]
  rule typeList(X : T,XTl) => T,typeList(XTl)                [structural]

--- l-value and loc
  syntax Exp ::= l-value ( K )
  syntax Val ::= loc ( Nat )
  rule <k> l-value(X) => loc(L) <_/k> <env_> X|->L <_/env> 
  rule <k> l-value(X => _._(this,X)) <_/k> <env> Env </env> if notBool(X in keys(Env))

 --- for array assignment, first evaluate the array and its index
  context l-value(_[[HOLE]])
  context l-value([HOLE][_])

  context l-value(_._([HOLE],_))
  rule <k> l-value(_._(obj(C,L), X) => lookupMember(<envStack>(C :: EnvC:Bag) EStack:List</envStack>, X)) <_/k>
       <store_> L |-> objEnv(<envStack_> (C :: EnvC) EStack </envStack>) <_/store>

  rule <k> l-value(lookup(L)) => loc(L) <_/k>


 
  syntax List{Val} ::= castAll ( List{Type} , List{Val} )
  macro castAll((T,Tl),(V,Vl))
      = cast(T,V), castAll(Tl, Vl)
  macro castAll(.List{Bottom},.List{Bottom}) = .List{Bottom}
  syntax Val ::= cast( Type , Val )
  macro cast(C, obj(_,L)) = obj(C,L) 
  macro cast(T, V2) = V2 [owise]





  --- looking up in object
  syntax CellLabel ::= envStack

  syntax K ::= lookupMember ( Bag , Id )

  --- lookup using object environment
  rule lookupMember(<envStack> _ :: <env_>  X |-> L:Nat <_/env> <_/envStack>,X) => lookup(L)

  --- recursing through the object environment stack
  rule lookupMember(<envStack> _ :: <env> Env </env>  => . <_/envStack>, X)
       if notBool(X in keys(Env)) [structural]


  syntax K ::= lookup Nat
  rule [lookup-loc]:
       <k> lookup L => V <_/k> <store_> L |-> V <_/store>

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

--- List{Val}
  syntax List{Val} ::= Val | List{Bottom} |  List{Val} , List{Val} [ditto]
  syntax List{Exp} ::= List{Val}

--- length
  syntax Nat ::= `| List{Id} `|
  macro |.List{Bottom}| = 0  
  macro |X, Xl:List{Id}| = sNat |Xl|

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
  macro subtypeAll((T:Type,Tl:List{Type}),(T':Type,Tl':List{Type}), Cls) = subtype(T,T', Cls) andBool subtypeAll(Tl, Tl', Cls)
  macro subtypeAll(.List{Bottom},.List{Bottom},_) = true 
  syntax Bool ::= subtype ( Type , Type , Bag ) 
  macro subtype(T, T, _) = true
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


