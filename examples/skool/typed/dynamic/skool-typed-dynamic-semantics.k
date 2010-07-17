--------------------------------------------
--- SKOOL-TYPED-DYNAMIC-SEMANTICS module ---
--------------------------------------------


---------------------
--- configuration ---
---------------------
kmod SKOOL-TYPED-DYNAMIC-CONFIG is including SKOOL-TYPED-DYNAMIC-DESUGARED-SYNTAX + K 

  syntax Val ::= Int | Bool

---<SKOOL added>
  syntax Val ::= Object
  syntax Object ::= oenv ( List )
---</SK00L added>

--- array values are wrapped as specific values
  syntax Val ::= array ( Type , Nat , Nat )  

--- function value; like arrays, functions also evaluate to 
---    their address (wrapped as a specific value)
  syntax Val ::= function( Type , Nat )
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
                     <genv> .Map </genv>
                     <store> .Map </store>
                     <in> .List </in>
                     <out> .List </out>
                     <return> none </return>
                     <nextLoc> 1 </nextLoc>
---<SKOOL added>
                     <obj> .List </obj>
                     <class> main </class>
                     <pgm>
                           <classes*>
                                    <className> Id:Id </className>
                                    <extends> Id:Id </extends>
                                    <stmts> .K </stmts>
                                    <fields> .K </fields>
                           </classes*>
                     </pgm>
---</SKOOL added>
                </T>



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

  syntax List{Type} ::= typeOf ( List{Val} ) [strict]
---<SKOOL added>
  syntax List{Bottom} ::= typeOf ( List{Bottom} ) 
  syntax Type ::= typeOf ( Val ) [strict]
  syntax Type ::= typeOf ( Int ) [strict]
  syntax Type ::= typeOf ( Bool ) [strict]
---<SKOOL added>
  macro typeOf(function(T, _)) = T 
  macro typeOf(array(T,_,_)) = T
  macro typeOf(I:Int) = int 
  macro typeOf(B:Bool) = bool 
  macro typeOf(none) = void 
  macro typeOf(V1:Val,V2:Val,Vl:List{Val}) = typeOf(V1),typeOf(V2,Vl) 
  macro typeOf(.List{Bottom}) = .List{Bottom} 
---<SKOOL added>
  macro typeOf(initVal(type(C:Id))) = type(C:Id)
  macro typeOf(oenv((C |-> Env:Map) OEnv:List)) = type(C)
---<SKOOL added>
  syntax List{Id} ::= idList ( List{IdType} ) 
  macro idList(.List{Bottom}) = .List{Bottom} 
  macro idList(X:Id : T:Type, XTl:List{IdType}) = X, idList(XTl) 

--- translation of a lists of typed names into a list of the corresponding types
  syntax List{Type} ::= typeList ( List{IdType} ) 
  macro typeList(.List{Bottom}) = .List{Bottom} 
  macro typeList(X : T,XTl) = T,typeList(XTl) 

--- List{Val}
  syntax List{Val} ::= Val |  List{Val} , List{Val} [ditto]
  syntax List{Exp} ::= List{Val}

--- length
  syntax Nat ::= `| List{Id} `|
  macro |.List{Bottom}| = 0  
  macro |X:Id,Xl:List{Bottom}| = sNat |Xl|

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
--- getloc: returns the "location" of an object X 
---  we use 0 as null and  start to allocate locations from 1 (see config. above)
  syntax Nat ::= null | getloc ( Id , List ) [strict]
  rule null => 0 [structural]

  rule getloc(X, ( ( C:Id |-> .) Oenv:List )) => getloc(X, Oenv ) [structural]
  rule getloc(X, ( ( C |-> ( Y:Id |-> L:Nat Env )) Oenv ))
       => if (X ==Bool Y) then L else getloc(X,  ((C |->  Env )Oenv)) fi [structural]
  rule getloc(X, .) => null [structural]

--- an object evironment layer is a map from the class name to the environm. corresp. to local fields
  syntax ListItem ::= Id |-> Map [metadata "latex(renameTo _\\ensuremath\\mapsto_)"]
--- the following is nedeed for stacking
  syntax ListItem ::=  [ Id , Map , K , Type ]
--- the following are needed at the creation of a new object and at a method call
  syntax K ::= restore ( List ) | discard
  syntax KLabel ::= create | invoke | addOEnvLayer 
--- the names for the local environment and the global environments for an object
  syntax Id ::= @local | @global
---   the internal name of a method is a pair [class, method-name], in order to be unique
---   (we assume that the name of a class in a program is unique)
  syntax Id ::= [ Id , Id ]

--- successor - ancestor relationship
  syntax  Bool ::= Type <: Type [strict]
  syntax  Bool ::= List{Top} <: List{Top} [strict]

  rule <k> T <: T => true <_/k> [structural]

  rule <k> (type(C1:Id) <: type(C2:Id)) 
           =>
           true
       <_/k>
       <pgm_>
            <classes_>
                     <className> C1 </className>
                     <extends> C2 </extends>
            <_/classes>
       <_/pgm>
       [structural]
  rule <k> (type(C1) <: type(C2)) 
           =>
          (type(C11) <: type(C2))
       <_/k>
       <pgm_>
            <classes_>
                     <className> C1 </className>
                     <extends> C11:Id </extends>
            <_/classes>
       <_/pgm>
       if C1 =/=Bool C2 andBool C1 =/=Bool C2
       [structural]
  rule Tl:List{Type} <: Tl => true [structural]
  rule T1:Type , Tl2:List{Type} <: T1':Type , Tl2':List{Type}
       =>
       (T1 <: T1') andBool (Tl2 <: Tl2')
       [structural]
---</SKOOL added>

endkm

---------------------
--- preprocessing ---
---------------------
kmod SKOOL-TYPED-DYNAMIC-PREPROCESSING is including SKOOL-TYPED-DYNAMIC-CONFIG

--- variable declaration; in the preprocessing phase only the global variables are processed 
--- this rule is also used process the local variables of a function
---   as a part of the function evaluation 

  rule <k> var X:Id : T:Type ; => .K <_/k> 
       <env> Env:Map => Env[L:Nat / X] </env> 
       <store_> .Map => L |-> initVal(T) <_/store>
       <nextLoc> L => sNat(L) </nextLoc> 

--- If an array is declared, then calculate its size; 

  context var X:Id[[HOLE]] : T ;
  rule <k> var X[N:Nat] : _`[`](T) ; => .K <_/k> 
       <env> Env => Env[L/X] </env>
       <store_>. => L |-> array(T, sNat L, N) <_/store>
       <nextLoc> L => sNat L +Nat N </nextLoc> 
  rule (sizeOf(array(_,_,N)) => N)   

---<SKOOL modified>

--- the following rule from Simple are removed (commented)
---  rule <k> function F:Id(Xl:List{Id}) S:Stmt => . <_/k> 
---       <env> Env => Env[L/F] </env> 
---       <nextLoc> L => L +Nat 2 </nextLoc> 
---       <store_>(.Map => L |-> function(sNat L) sNat(L) |-> lambda(Xl,S))<_/store>

--- the followings are added

--- a class traversal
  --- the following is used to know where a class preprocessing is finished
  syntax K ::= preprocessClass ( Id )
  rule <k> class C1:Id extends C2:Id { Ss:Stmts } => preprocessClass (C1) <_/k>
       <pgm_> . => <classes_>
                           <className> C1 </className>          
                           <extends> C2 </extends>
                           <stmts> Ss </stmts>
                   <_/classes>
       <_/pgm>

--- variable member declaration
 
  rule <k> preprocessClass(C:Id) <_/k>
       <pgm_>
            <classes_>
                     <className> C </className>
                     <fields_> . => var X : T; </fields>
                     <stmts> var X:Id : T; => .K <_/stmts>
            <_/classes>
       <_/pgm>

  rule <k> preprocessClass(C) <_/k>
       <pgm_>
            <classes_>
                     <className> C </className>
                     <fields_> .K => var X[ N:Nat ] : _`[`](T); </fields>
                     <stmts> var X[ N:Nat ] : _`[`](T); => .K <_/stmts>
            <_/classes>
       <_/pgm>

--- method declaration

  rule <k> preprocessClass(C) <_/k>
       <pgm_>
            <classes_>
                     <className> C </className>
                     <stmts> method F:Id(XTl:List{IdType}) : T S:Stmt => .K <_/stmts>
            <_/classes>
       <_/pgm>
       <env> Env:Map => Env[L/[C, F]] </env>  
       <nextLoc> L:Nat => L +Nat 2 </nextLoc> 
       <store_>(.Map => L |-> function(typeList(XTl) -> T, sNat L) sNat(L) |-> lambda(idList(XTl), S))<_/store>

--- finish processing a class

  rule <k> preprocessClass(C) => .K <_/k>
        <classes_>
                <className> C </className>
                ( <stmts> .K </stmts> => .Bag )
       <_/classes>

--- when we are done with the first pass (preprocessing), i.e., the computation and genv are empty,
---   call main and initialize the global environment
---  the following is removed
---  rule <k> . => main(); </k> <env> Env </env> <genv> . => Env </genv>

---    ... and the following added:
  rule <k> . => new_`(_`)(main, .List{Bottom}) </k>
       <env> Env => . </env>
       <genv> . => Env </genv>
       <class> _ => main </class>

---</SKOOL modified>

endkm

-------------------------------------
--- Evaluation of the expressions ---
-------------------------------------
kmod SKOOL-TYPED-DYNAMIC-EXPR-EVALUATION is including SKOOL-TYPED-DYNAMIC-CONFIG 

--- variable lookup

---<SKOOL modified>
---  rule <k> X:Id => V:Val <_/k>  
---       <env_> X |-> L:Nat <_/env>
---       <store_> L |-> V <_/store> 

  rule <k> X:Id => Store(getloc(X, ((@local |-> Env) ((C |-> Env1) Oenv)(@global |-> GEnv)))) <_/k>
       <env> Env:Map </env>
       <genv> GEnv:Map </genv>
       <obj_> (C:Id |-> Env1:Map) Oenv:List </obj>
       <class> C </class>
       <store> Store:Map </store>  
  rule <k> this =>  oenv(Oenv) <_/k>
       <obj> Oenv </obj>
---</SKOOL modified>

--- arithmetic expressions

  rule <k> ++X => I:Int +Int 1 <_/k>
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

  rule <k> array(_,L,_)[N:Nat] => Sigma:Map(L +Int N) <_/k> <store> Sigma </store> .
                                --- untyped SKOOL does not check array bounds
--- read expression

  rule <k> read() => I <_/k> <in> ListItem(I) => . <_/in>

---<SKOOL added>
--- new operator
---   the semantics of the new operator consists of two actions: memory allocation for the new object
---   and the execution of the statements included in the constructor
---   the current class, environment and object are stored on the stack

  rule <k> (new_`(_`)(C:Id, Vl:List`{Val`}))~>K:K => create(C)~>invoke(_`(_`)(C, Vl))</k>
       <env> Env:Map => . </env>
       <obj> Oenv:List => . </obj>
       <class> C1:Id => C </class>
       <return> T:Type => type(C) </return>
       <fstack> . => [ C1, Env, (discard ~> this ~> restore(Oenv)~>K), T ] <_/fstack>
       if C =/=Bool main
  rule <k> (new_`(_`)(C:Id, Vl))~>K => create(C)~>invoke(_`(_`)(C, Vl))</k>
       <env> Env => . </env>
       <obj> Oenv:List => . </obj>
       <class> C1:Id => C </class>
       <return> T => type(C) </return>
       <fstack> . => [ C1, Env, (restore(Oenv)~>K), type(C) ] <_/fstack>
       if (C ==Bool main) andBool (K ==Bool .) 

--- create a new object (memory allocation)
---   usually, an object is an instance of a class from an hierarchy
---   a memory object representation is a layered structure: for each class lying on the path 
---   from the current class to the root of the hierarchy there is a layer including the memory
---   allocation for the variable members of that class
  rule <k> create(C) => Fs ~> addOEnvLayer(C:Id) ~> create(C1) <_/k>
       <pgm_>
            <classes_>
                   <className> C </className>
                   <extends> C1 </extends>
                   <fields> Fs:Stmts </fields>
            <_/classes>
       <_/pgm>
       if C1 =/=Bool object
  rule <k> create(C) => Fs ~> addOEnvLayer(C:Id) <_/k>
       <pgm_>
            <classes_>
                   <className> C </className>
                   <extends> object </extends>
                   <fields> Fs:Stmts </fields>
            <_/classes>
       <_/pgm>

--- add a new tagged environment layer to the  current object
  rule <k> addOEnvLayer(C) => . <_/k>
       <env> Env => . </env>
       <obj_> . => (C |-> Env) </obj>

--- discards the value (item?) from the top of the computation
  rule <k> V:Val ~> discard => . <_/k>     

--- restore the current object
  rule <k> V ~> restore(Oenv) => V <_/k> 
       <obj> _ => Oenv </obj>

--- instanceOf operator

  rule <k> _instanceOf_(oenv( (C |-> Env) Oenv), C1) => true <_/k> if (C ==Bool C1)
  rule <k> _instanceOf_(oenv( (C |-> Env) Oenv), C1) => _instanceOf_(oenv(Oenv), C1) <_/k>
       if (C =/=Bool C1) 
  rule <k> _instanceOf_( oenv(.), C1) => false <_/k>

---</SKOOL added>
endkm

---------------------
--- method call ---
---------------------
kmod SKOOL-TYPED-DYNAMIC-FUNCTION-CALL is including SKOOL-TYPED-DYNAMIC-CONFIG


---<SKOOL modified>

--- the environment and the computation are pushed in the stack at each function call

---  syntax ListItem ::=  ( Map , K )
---  rule <k> _`(_`)(function(L),Vl:List`{Val`})~>K:K => S:Stmt~>return(0); </k> 
---       <fstack> .List => (Env:Map,K:K) <_/fstack>
---       <env> Env => GEnv:Map[N:Nat..N+Nat|Xl| / getList{K}(Xl)] </env>
---       <genv> GEnv </genv>
---       <store_> L:Nat |-> lambda(Xl:List{Id},S) (. => N..N+Nat|Xl| |-> getList{K}(Vl)) <_/store>
---       <nextLoc> N => N +Nat |Xl| </nextLoc>

---  rule <k> return(V:Val); ~> _ => V ~> K </k>
---       <fstack> (Env,K) => . <_/fstack>
---       <env> _ => Env </env> 

--- method call: preprocessing
  rule <k> (_._`(_`)(oenv((C:Id |-> Env:Map) Oenv:List), F:Id, Vl:List{Val})) ~> K:K 
           =>
           invoke(_`(_`)(F:Id, Vl)) </k>
       <class> C1:Id => C:Id </class>
       <obj> Oenv1:List => (C |-> Env) Oenv </obj>
       <return> T:Type </return>
       <env> Env1:Map => . </env>
       <fstack> .List => [ C1, Env1, (restore(Oenv1)~>K), T ] <_/fstack>
  rule <k> super_`(_`)(F, Vl) ~> K => invoke(_`(_`)(F:Id, Vl)) </k>
       <class> C => C1 </class>
       <env> Env1 => . </env>
       <fstack> .List => [ C, Env1, K, type(C) ] <_/fstack>
       <pgm_>
            <classes_>
                   <className> C </className>
                   <extends> C1 </extends>
            <_/classes>
       <_/pgm>

  syntax K ::= floc ( Nat , List{Val} )
  rule <k> invoke(_`(_`)(F:Id, Vl))
           =>
           floc(getloc( [C, F], ( @global |-> GEnv:Map )), Vl)
       <_/k>
       <class> C </class>
       <genv> GEnv </genv>
       if getloc( [C, F], ( @global |-> GEnv )) =/=Bool null 
  rule <k> floc(L:Nat, Vl)
           =>
           (_`(_`)(function(Tl:List{Type} -> T, sNat L), Vl))
       <_/k>
       <class> C </class>
       <return> T':Type => T </return>
       <store_> L |->  function(Tl:List{Type} -> T, sNat L) <_/store>
  rule <k> invoke(_`(_`)(F:Id, Vl))
           =>
           invoke(_`(_`)(F:Id, Vl))
       <_/k>
       <class> C => C1 </class>
       <pgm_>
            <classes_>
                   <className> C </className>
                   <extends> C1 </extends>
            <_/classes>
       <_/pgm>
       <genv> GEnv </genv>
       if getloc( [C, F], ( @global |-> GEnv )) ==Bool null 

--- method call: function value loading 
--- <OO modified>: the global environment not longer included in the local function call environment
  syntax K ::= functionLoad 
  rule <k> (_`(_`)(function(Tl -> T, L),Vl:List{Val}))
           =>
           typeOf(Vl) ~> functionLoad ~> (_`(_`)(function(Tl -> T, L),Vl:List{Val}))
       <_/k> 
  rule <k>
           Tl':List{Type} ~> functionLoad ~> (_`(_`)(function(Tl -> T, L),Vl:List{Val}))
           =>
           (Tl' <: Tl) ~> functionLoad ~> (_`(_`)(function(Tl -> T, L),Vl:List{Val})) <_/k> 
  rule <k>
           true ~> functionLoad ~> (_`(_`)(function(Tl -> T, L),Vl:List{Val}))~>K
           =>
           S:Stmt ~> return(initVal(T));
       </k>
       <env> _ => .Map[N..N+Nat|Xl| / getList{K}(Xl:List{Id})] </env>
       <genv> GEnv </genv>
       <store_> L:Nat |-> lambda(Xl,S) (. => N:Nat..N+Nat|Xl| |-> getList{K}(Vl)) <_/store>
       <nextLoc> N => N +Nat |Xl| </nextLoc>
---       if typeOf(Vl) <: Tl

--- returning from a method call
  syntax K ::= returnCheckType 
  rule <k> return(V:Val);  => typeOf(V) ~> returnCheckType ~> return(V);  <_/k>
 
  rule <k> T1:Type ~> returnCheckType ~> return(V:Val); ~> _ => V ~> K </k>
       <fstack> [ C, Env, K, T':Type ] => .List <_/fstack>
       <class> _ => C </class>
       <env> _ => Env </env>
       <return> T => T' </return>
       if T1 <: T
---       if typeOf(V) <: T

---</SKOOL modified>
endkm

------------------------------
--- instruction processing ---
------------------------------
kmod SKOOL-TYPED-DYNAMIC-INSTR-PROCESSING is including SKOOL-TYPED-DYNAMIC-CONFIG 

  rule {} => .
  rule <k> {Ss:Stmts} => Ss~>env(Env) <_/k> <env> Env:Map </env> 
  rule S1:Stmt S2:Stmt => S1~>S2 

---<SKOOL modified> 
--- this is just to safely keep the trace (it could work without it, as well)
  syntax K ::= assignLeftValue ( Nat )
  rule <k> (_=_;(X:Id, V:Val))
           =>
           assignLeftValue(getloc(X, ((@local |-> Env) ((C |-> Env1) Oenv)(@global |-> GEnv)))) ~> (_=_;(X:Id, V:Val)) <_/k> 
       <env> Env:Map </env> 
       <genv> GEnv:Map </genv>
       <obj_> (C:Id |-> Env1:Map) Oenv:List </obj>
       <class> C </class>
  rule <k> assignLeftValue(L:Nat) ~> (_=_;(X:Id, V:Val))
       =>
       typeOf(V) <: typeOf(V1) ~>  assignLeftValue(L) ~> (_=_;(X:Id, V:Val)) <_/k> 
       <store_> L |-> V1:Val <_/store>
---       if typeOf(V) <: typeOf(V1) ==Bool true
  rule <k> true ~> assignLeftValue(L) ~> (_=_;(X:Id, V:Val)) => . <_/k> 
       <store> Sigma:Map => Sigma [ V / L ] </store>
---</SKOOL modified>

 --- for array assignment, first evaluate the array and its index
  context _[[HOLE]]=_;
  context [HOLE][_]=_;
---<SKOOL typed modified>
  syntax K ::= assignArray
  rule <k> array(T:Type, L:Nat,M:Nat)[N:Nat]=V;
           =>
           typeOf(V) <: T ~> assignArray ~> array(T:Type, L:Nat,M)[N:Nat]=V; <_/k>
  rule <k> true ~> assignArray ~> array(T:Type, L:Nat,_)[N:Nat]=V; => . <_/k>
       <store> Sigma => Sigma[V/(L +Int N)] </store> 
---       if typeOf(V) <: T ==Bool true

---</SKOOL type modified>
  rule V; => . 
  rule if true then S:Stmt else _ => S:Stmt
  rule if false then _ else S => S 
  rule <k> while B:Exp do S  => if B then {S while B do S} else {} <_/k>
  rule <k> write(I:Int); => . <_/k> <out_> . => ListItem(I) </out>
endkm

-----------------
--- semantics ---
-----------------
kmod SKOOL-TYPED-DYNAMIC-SEMANTICS is 
  including SKOOL-TYPED-DYNAMIC-PREPROCESSING +
            SKOOL-TYPED-DYNAMIC-FUNCTION-CALL +
            SKOOL-TYPED-DYNAMIC-EXPR-EVALUATION +
            SKOOL-TYPED-DYNAMIC-INSTR-PROCESSING
endkm


