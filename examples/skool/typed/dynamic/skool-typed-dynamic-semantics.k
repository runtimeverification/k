--------------------------------------------
--- SKOOL-TYPED-DYNAMIC-SEMANTICS module ---
--------------------------------------------


---------------------
--- configuration ---
---------------------
kmod SKOOL-TYPED-DYNAMIC-SEMANTICS is including SKOOL-TYPED-DYNAMIC-DESUGARED-SYNTAX + K 

  syntax Val ::= Int | Bool

---<SKOOL added>
  syntax Val ::= objAddress ( Id , Nat ) [latex "obj({#1},{#2})"]
  syntax Val ::= obj ( Bag ) [latex "{#1}"]
---</SK00L added>

--- array values are wrapped as specific values
  syntax Val ::= array ( Type , Nat , Nat )  

--- function value; like arrays, functions also evaluate to 
---    their address (wrapped as a specific value)
---<SKOOL modified>
--- added object and class info for functions
  syntax Val ::= function ( Type , K ,  Nat )
---</SKOOL modified>
  ---  op function : Nat -> Val   
  syntax Val ::= lambda ( List{Id} , Stmt ) [metadata "latex(renameTo \\ensuremath\\lambda_._)"]

--- the values are expressions
  syntax Exp ::= Val

--- We have to subsort all the syntactic categories to K, and the lists of values
--- to KResult.  Recall that the second argument of a method application is a list
--- of expressions, so that becomes a result when it becomes a list of values

  syntax K ::= Stmts | List{Exp} | List{Type} | List{IdType} | List{Top}
  syntax KResult ::= List{Val} 

  configuration <T> 
                     <k> K:K </k>
                     <fstack> .List </fstack>
                     <env> .Map </env>
                     <store> .Map </store>
                     <in> .List </in>
                     <out> .List </out>
                     <return> none </return>
                     <nextLoc> 1 </nextLoc>
---<SKOOL added>
                     <crntObj> .K </crntObj>
                     <classes>
                           <class*> 
                                    <className> Id:Id </className>
                                    <extends> Id:Id </extends>
                                    <declarations> .K </declarations>
                           </class*>
                     </classes>
---</SKOOL added>
                </T>

  syntax CellLabel ::= envStack 


-------------------------------
--- declarations processing ---
-------------------------------

--- variable declaration; in the preprocessing phase only the global variables are processed 
--- this rule is also used to process the local variables of a function
---   as a part of the function evaluation 

  rule [decl-variable]: <k> var X:Id : T:Type ; => .K <_/k> 
       <env> Env:Map => Env[L:Nat / X] </env> 
       <store_> .Map => L |-> initVal(T) <_/store>
       <nextLoc> L => sNat(L) </nextLoc> 

--- If an array is declared, then calculate its size; 

  context var X:Id[[HOLE]] : T ;
  rule [decl-array]: <k> var X[N:Nat] : _`[`](T) ; => .K <_/k> 
       <env> Env => Env[L/X] </env>
       <store_>. => L |-> array(T, sNat L, N) sNat(L)..sNat(L)+Nat N |-> initVal(T) <_/store>
       <nextLoc> L => sNat L +Nat N </nextLoc> 
  rule (sizeOf(array(_,_,N)) => N)   

---<SKOOL modified>

  rule [decl-method]: <k> (method F:Id(XTl:List{IdType}) : Tp S:Stmt => .) <_/k> 
       <env> Env => Env[L/F] </env> 
       <nextLoc> L => L +Nat 2 </nextLoc> 
       <crntObj> Obj:K </crntObj> 
       <store_>(.Map => L |-> function`(_`,_`,_`)((typeList(XTl)->Tp), Obj, sNat L) 
                  sNat(L) |-> lambda(idList(XTl),S))<_/store>

--- the followings are added

--- a class traversal
  rule <k> class C1:Id extends C2:Id { Ss:Stmts } => .K <_/k>
       <classes_> (. => <class_>
                           <className> C1 </className>          
                           <extends> C2 </extends>
                           <declarations> Ss </declarations>
                   <_/class>)
       <_/classes>

--- variable member declaration

--- when we are done with the first pass (preprocessing), i.e., the computation and env must be empty, as we expect no global environment
---   call main 
---  the following is removed
---  rule <k> . => main(); </k> <env> Env </env> <genv> . => Env </genv>

---    ... and the following added:
  rule [call-main]: <k> . => new_`(_`)(main, .List{Bottom}) </k>
       <env> .Map </env>


---</SKOOL modified>

-------------------
--- Expressions ---
-------------------

--- variable lookup

  rule [lookup-var]: <k> X:Id => V:Val <_/k>  
       <env_> X |-> L:Nat <_/env>
       <store_> L |-> V <_/store> 

---<SKOOL extension>
  --- if an id is not in the local environment assume it's a field 
  --- static lookup for fields
  rule [lookup-field]: <k> X:Id => _._(this,X) <_/k>
       <env> Env:Map </env>
       if notBool(X in keys(Env)) [structural]

  rule [this]: <k> this => Obj <_/k>  
       <crntObj> Obj </crntObj>

  context ('_._(`[HOLE`]:K,,_)) if (`[HOLE`]:K =/=Bool super)

  rule [super]: <k> _._((super => objAddress(C',L)),X) <_/k>
       <crntObj> objAddress(C,L) </crntObj>
       <className> C </className> 
       <extends> C' </extends>

  syntax K ::= lookupF ( Bag , Id )
  syntax K ::= location ( Nat ) 

  --- looking up in object
  rule <k> _._(objAddress(C,L),X) => lookupF(<envStack>  (C :: EnvC:Bag) EStack:List </envStack>, X) <_/k>
      <store_> L |-> obj(<envStack_> (C :: EnvC) EStack </envStack>) <_/store>
 
  --- lookup using object environment
  rule lookupF(<envStack> _ :: <env_>  X |-> L:Nat <_/env> <_/envStack>,X) => lookup(L)  

  --- recursing through the object environment stack
  rule lookupF(<envStack> _ :: <env> Env </env>  => . <_/envStack>, X)
       if notBool(X in keys(Env)) [structural]

---</SKOOL extension>

--- arithmetic expressions

  rule [pre-inc]: <k> ++X => I:Int +Int 1 <_/k>
       <env_> X |-> L:Nat <_/env>
       <store_> L |-> (I => I +Int 1) <_/store> 
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

--- array component value:

  rule [array-indexing]: array(_,L,M:Nat)[N:Nat] => lookup(L +Int N) 
    if N >=Nat 0 andBool N <=Nat M [structural]
  syntax K ::= lookup Nat
  rule [lookup-loc]: <k> lookup L => V <_/k> <store_> L |-> V <_/store>

--- read expression

  rule [input]: <k> read() => I <_/k> <in> (ListItem(I) => .) <_/in>

---<SKOOL added>
--- new operator
---   the semantics of the new operator consists of two actions: memory allocation for the new object
---   and the execution of the statements included in the constructor
---   the current class, environment and object are stored on the stack

  rule [new-object]: <k> (new_`(_`)(C:Id, Vl:List`{Val`}))~>K:K => create(C) ~> _`(_`)(C, Vl); return this ; </k>
       <env> Env:Map => . </env>
       <crntObj> Obj => objAddress(object,L) </crntObj>
       <return> T:Type => C </return>
       <nextLoc> L => sNat L </nextLoc>
       <store_> . => L |-> obj(<envStack> object::<env> .Map </env> </envStack>) <_/store>
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
  rule <k> create(object) => .K <_/k>

--- add a new tagged environment layer to the  current object
  rule <k> addEnvLayer => . <_/k>
       <env> Env => . </env>
       <crntObj> objAddress(C,L) </crntObj>
       <store_> L |-> obj(<envStack> . => (C::<env>Env</env>)<_/envStack>)
       <_/store>

  rule <k> setCrntClass(C) => . <_/k>  
       <crntObj> objAddress((_ => C),_) </crntObj>

--- instanceOf operator

  rule [instanceOf]: <k> _instanceOf_(V, C) => subtype(typeOf(V),C,Cls) <_/k>
       <classes> Cls:Bag </classes>

---</SKOOL added>

---------------------
--- method call ---
---------------------

---<SKOOL modified>

  --- dynamic method dispatch: methods are looked up from top of object

  --- rule <k> (X => _._(this,X))(_) <_/k> ?
  rule <k> _`(_`)((X => _._(this,X)),_) <_/k>

  context '_`(_`)('_._(`[HOLE`]:K,,_),,_) if `[HOLE`]:K =/=Bool super 

  rule <k> '_`(_`)(('_._(objAddress(_,L),,X) => lookupF(Envs:Bag, X)),,_) <_/k>
      <store_> L |-> obj(Envs) <_/store>

  --- except for super which should lookup method statically
  rule <k> '_`(_`)(('_._(super,,X) => lookupF(<envStack> EStack </envStack>, X)),,_) <_/k>
      <crntObj> objAddress(C,L) </crntObj>
      <store_> L |-> obj(<envStack_>  (C :: EnvC:Bag) EStack:List </envStack>) <_/store>


  rule <k> '_`(_`)((lookup(L) => V),,_) <_/k>
       <store_> L |-> V <_/store>



--- the environment and the computation are pushed in the stack at each function call


 rule <k> _`(_`)(function`(_`,_`,_`)(Tpl:List{Type}->Tp,Obj,L),Vl:List{Val}) ~> K => S ~> return(initVal(Tp)); </k>
       <fstack> . => Env # K # Obj' # Tp' <_/fstack>
       <crntObj> Obj':K => Obj </crntObj>
       <env> Env =>  getList{K}(Xl) |-> N..N+Nat|Xl| </env>
       <return> Tp':Type => Tp </return>
       <store_> L|->lambda(Xl:List{Id},S) (. => N..N+Nat|Xl| |-> getList{K}(Vl)) <_/store>
       <nextLoc> N => N +Nat |Xl| </nextLoc>
       <classes> Cls </classes>
    if subtype(typeOf(Vl), Tpl, Cls)

  rule <k> return(V); ~> _ => V ~> K </k>
       <fstack> Env # K # Obj # Tp' => . <_/fstack>
       <crntObj> _ => Obj </crntObj>
       <env> _ => Env </env>
       <return> Tp => Tp' </return>
       <classes> Cls </classes>
    if subtype(typeOf(V), Tp, Cls)

---</SKOOL modified>

------------------------------
--- instruction processing ---
------------------------------
  rule {} => .
  rule <k> {Ss:Stmts} => Ss~>env(Env) <_/k> <env> Env:Map </env> 
  rule S1:Stmt S2:Stmt => S1~>S2 

---<SKOOL modified> 
  rule <k> X=V1; => . <_/k> <env_> X|->L <_/env> <store_> L|->(V2=>update(V2,V1)) <_/store>
       <classes> Cls </classes>
    if subtype(typeOf(V1), typeOf(V2),Cls)

  rule <k> (X => _._(this,X)) =_; <_/k> <env> Env </env> if notBool(X in keys(Env))
  
  context _._([HOLE],_)=_;

 ---similar lookup as for variables
  rule <k> '_=_;((_._(objAddress(C,L), X)  => lookupF(<envStack>  (C :: EnvC) EStack:List </envStack>, X)),,_) <_/k>
      <store_> L |-> obj(<envStack_> (C :: EnvC) EStack </envStack>) <_/store>
 
  syntax K ::= update ( K , K )
  macro update(objAddress(C,_), objAddress(_,L)) = objAddress(C,L) 
  macro update(V1,V2) = V2 [owise]

---</SKOOL modified>

 --- for array assignment, first evaluate the array and its index
  context _[[HOLE]]=_;
  context [HOLE][_]=_;
---<SKOOL typed modified>
  rule <k> '_=_;(lookup(L),,V1) => . <_/k>
       <store_> L |-> (V2 => update(V2,V1)) <_/store> 
       <classes> Cls </classes>
       if subtype(typeOf(V1), typeOf(V2), Cls)
---</SKOOL type modified>
  rule V; => . 
  rule if true then S:Stmt else _ => S:Stmt
  rule if false then _ else S => S 
  rule <k> while E:Exp do S  => if E then {S while E do S} else {} <_/k>
  rule <k> write(I:Int); => . <_/k> <out_> . => ListItem(I) </out>


----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------


  syntax Val ::=
                 initVal ( Type )
               | none 
  macro initVal(int) = 0 
  macro initVal(bool) = false 
  macro initVal(void) = none 
  macro initVal(_`[`](T:Type)) = array(_`[`](T),0,0) 
  macro initVal(C:Id) = objAddress(C,0)

  syntax List{Type} ::= typeOf ( List{Val} ) [strict]
---<SKOOL added>
---  syntax List{Bottom} ::= typeOf ( List{Bottom} ) [ditto]
---  syntax Type ::= typeOf ( Val ) [ditto]
---</SKOOL added>

  macro typeOf(function`(_`,_`,_`)(T,_,_)) = T 
  macro typeOf(array(T,_,_)) = T
  macro typeOf(I:Int) = int 
  macro typeOf(B:Bool) = bool 
  macro typeOf(none) = void 
  macro typeOf(V1:Val,V2:Val,Vl:List{Val}) = typeOf(V1),typeOf(V2,Vl) 
  macro typeOf(.List{Bottom}) = .List{Bottom} 
---<SKOOL added>
  macro typeOf(objAddress(C,_)) = C
  macro typeOf(obj(<envStack> C :: _ <_/envStack>)) = C
---</SKOOL added>
  syntax List{Id} ::= idList ( List{IdType} ) 
  macro idList(.List{Bottom}) = .List{Bottom} 
  macro idList(X:Id : T:Type, XTl:List{IdType}) = X, idList(XTl) 

--- translation of a lists of typed names into a list of the corresponding types
  syntax List{Type} ::= typeList ( List{IdType} ) 
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

  syntax Bool ::= subtype ( List{Type} , List{Type} , Bag ) 
  macro subtype((Tp1:Type,Tp1':Type,Tpl1:List{Type}),(Tp:Type,Tp':Type,Tpl:List{Type}), Cls) = subtype(Tp1,Tp, Cls) andBool subtype((Tp1',Tpl1), (Tp',Tpl), Cls)
  macro subtype(.List{Bottom},.List{Bottom},_) = true 
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


