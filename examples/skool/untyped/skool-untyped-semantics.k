--------------------------------------
--- SKOOL-UNTYPED-SEMANTICS module ---
--------------------------------------


---------------------
--- configuration ---
---------------------
kmod SKOOL-UNTYPED-CONFIG is including SKOOL-UNTYPED-DESUGARED-SYNTAX + K 

  syntax Val ::= Int | Bool

---<SKOOL added>
  syntax Val ::= Object
  syntax Object ::= oenv ( List )
---</SK00L added>

--- array values are wrapped as specific values
  syntax Val ::= array ( Nat , Nat )  

--- function value; like arrays, functions also evaluate to 
---    their address (wrapped as a specific value)
  syntax Val ::= function( Nat )
  ---  op function : Nat -> Val   
  syntax Val ::= lambda ( List{Id} , Stmt ) [metadata "latex(renameTo \\ensuremath\\lambda_._)"]

--- the values are expressions
  syntax Exp ::= Val

--- We have to subsort all the syntactic categories to K, and the lists of values
--- to KResult.  Recall that the second argument of a method application is a list
--- of expressions, so that becomes a result when it becomes a list of values

  syntax K ::= Stmts | List{Exp}
  syntax KResult ::= List{Val}

  configuration <T> 
                     <k> K:K </k>
                     <fstack> .List </fstack>
                     <env> .Map </env>
                     <genv> .Map </genv>
                     <store> .Map </store>
                     <in> .List </in>
                     <out> .List </out>
                     <nextLoc> 1 </nextLoc>
---<SKOOL added>
                     <obj> .List </obj>
                     <class> main </class>
                     <pgm>
                           <classes*>
                                    <className> Id:Id </className>
                                    <extends> Id:Id </extends>
                                    <fields> .K </fields>
                           </classes*>
                     </pgm>
---</SKOOL added>
                </T>



----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------
--- List{Val}
  syntax List{Val} ::= Val |  List{Val} , List{Val} [ditto]
  syntax List{Exp} ::= List{Val}

--- length
  syntax Nat ::= `| List{Id} `|
  macro |.List{Id}| = 0  
  macro |X:Id,Xl:List{Id}| = sNat |Xl|

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

  rule getloc(X, ( ( C:Id :: .) Oenv:List )) => getloc(X, Oenv ) [structural]
  rule getloc(X, ( ( C :: ( Y:Id |-> L:Nat Env )) Oenv ))
       => if (X ==Bool Y) then L else getloc(X,  ((C ::  Env )Oenv)) fi [structural]
  rule getloc(X, .) => null [structural]

--- an object evironment layer is a map from the class name to the environm. corresp. to local fields
  syntax ListItem ::= Id :: Map [metadata "latex(renameTo _\\ensuremath\\mathrel{::}_)"]
--- the following is nedeed for stacking
  syntax ListItem ::=  [ Id , Map , K ]
--- the following are needed at the creation of a new object and at a method call
  syntax K ::= restore ( List ) | discard
  syntax KLabel ::= create | invoke | addOEnvLayer 
--- the names for the local environment and the global environments for an object
  syntax Id ::= @local | @global
---   the internal name of a method is a pair [class, method-name], in order to be unique
---   (we assume that the name of a class in a program is unique)
  syntax Id ::= [ Id , Id ]

---</SKOOL added>

endkm

---------------------
--- preprocessing ---
---------------------
kmod SKOOL-UNTYPED-PREPROCESSING is including SKOOL-UNTYPED-CONFIG

--- variable declaration; in the preprocessing phase only the global variables are processed 
--- this rule is also used process the local variables of a function
---   as a part of the function evaluation 

  rule <k> var X:Id ; => .K <_/k> 
       <env> Env:Map => Env[L:Nat / X] </env> 
       <store_> .Map => L |-> 0 <_/store>
       <nextLoc> L => sNat(L) </nextLoc> 

--- If an array is declared, then calculate its size; 

  context var X:Id[[HOLE]];
  rule <k> var X[N:Nat]; => . <_/k> 
       <env> Env => Env[L/X] </env>
       <store_>. => L |-> array(sNat L, N) <_/store>
       <nextLoc> L => sNat L +Nat N </nextLoc> 
  rule (sizeOf(array(_,N)) => N)   

---<SKOOL modified>

--- the following rule from Simple are removed (commented)
---  rule <k> function F:Id(Xl:List{Id}) S:Stmt => . <_/k> 
---       <env> Env => Env[L/F] </env> 
---       <nextLoc> L => L +Nat 2 </nextLoc> 
---       <store_>(.Map => L |-> function(sNat L) sNat(L) |-> lambda(Xl,S))<_/store>


--- the followings are added


--- a class traversal
  --- the following is used to know where a class preprocessing is finished
  syntax K ::= preprocessClass ( Id ) | preprocessClassDone
  rule <k> class C1:Id extends C2:Id { Ss:Stmts } => preprocessClass (C1) <_/k>
       <pgm_> . => <classes_>
                           <className> C1 </className>          
                           <extends> C2 </extends>
                           <fields> Ss ~> preprocessClassDone </fields>
                   <_/classes>
       <_/pgm>

--- variable member declaration 
  rule <k> preprocessClass(C:Id) <_/k>
       <pgm_>
            <classes_>
                     <className> C </className>
                     <fields> var X:Id; ~> K:K => K ~> var X:Id; </fields>
            <_/classes>
       <_/pgm>
       
  rule <k> preprocessClass(C) <_/k>
       <pgm_>
            <classes_>
                     <className> C </className>
                     <fields> var X[ N:Nat ]; ~> K => K ~> var X[ N ]; </fields>
            <_/classes>
       <_/pgm>
 
--- method declaration

  rule <k> preprocessClass(C:Id) <_/k>
       <pgm_>
            <classes_>
                     <className> C </className>
                     <fields> method F:Id(Xl:List{Id}) S:Stmt => . <_/fields>
            <_/classes>
       <_/pgm>
       <env> Env:Map => Env[L/[C, F]] </env>  
       <nextLoc> L:Nat => L +Nat 2 </nextLoc> 
       <store_>(.Map => L |-> function(sNat L) sNat(L) |-> lambda(Xl,S))<_/store>

--- finish processing a class

  rule <k> preprocessClass(C) => .K <_/k>
       <classes_>
                <className> C </className>
                <fields> preprocessClassDone => . <_/fields>
       <_/classes>

--- when we are done with the first pass (preprocessing), i.e., the computation and genv are empty,
---   call main and initialize the global environment
---  the following is removed
---  rule <k> . => main(); </k> <env> Env </env> <genv> . => Env </genv>

---    ... and the following added:
  rule <k> . => new_`(_`)(main, .List{Id}) </k>
       <env> Env => . </env>
       <genv> . => Env </genv>
       <class> _ => main </class>

---</SKOOL modified>

endkm

-------------------------------------
--- Evaluation of the expressions ---
-------------------------------------
kmod SKOOL-UNTYPED-EXPR-EVALUATION is including SKOOL-UNTYPED-CONFIG 

--- variable lookup

---<SKOOL modified>
---  rule <k> X:Id => V:Val <_/k>  
---       <env_> X |-> L:Nat <_/env>
---       <store_> L |-> V <_/store> 

  rule <k> X:Id => Store(getloc(X, ((@local :: Env) ((C :: Env1) Oenv)(@global :: GEnv)))) <_/k>
       <env> Env:Map </env>
       <genv> GEnv:Map </genv>
       <obj_> (C:Id :: Env1:Map) Oenv:List </obj>
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
  rule T1:Bool and T2:Bool => T1 andBool T2 
  rule T1 or T2 => T1 orBool T2 
  rule not(T:Bool) => notBool(T) 

--- array component value:
---    first arg. is the location of the first element in the array, and 
---    the second argument is the array size (= the index)

  rule <k> array(L,_)[N:Nat] => Sigma:Map(L +Int N) <_/k> <store> Sigma </store> .
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
       <fstack> . => [ C1, Env, (discard ~> this ~> restore(Oenv)~>K) ] <_/fstack>
       if C =/=Bool main
  rule <k> (new_`(_`)(C:Id, Vl))~>K => create(C)~>invoke(_`(_`)(C, Vl))</k>
       <env> Env => . </env>
       <obj> Oenv:List => . </obj>
       <class> C1:Id => C </class>
       <fstack> . => [ C1, Env, (restore(Oenv)~>K) ] <_/fstack>
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
       <obj_> . => (C :: Env) </obj>

--- discards the value (item?) from the top of the computation
  rule <k> V:Val ~> discard => . <_/k>     

--- restore the current object
  rule <k> V ~> restore(Oenv) => V <_/k> 
       <obj> _ => Oenv </obj>

--- instanceOf operator

  rule <k> _instanceOf_(oenv( (C :: Env) Oenv), C1) => true <_/k> if (C ==Bool C1)
  rule <k> _instanceOf_(oenv( (C :: Env) Oenv), C1) => _instanceOf_(oenv(Oenv), C1) <_/k>
       if (C =/=Bool C1) 
  rule <k> _instanceOf_( oenv(.), C1) => false <_/k>

---</SKOOL added>
endkm

---------------------
--- method call ---
---------------------
kmod SKOOL-UNTYPED-FUNCTION-CALL is including SKOOL-UNTYPED-CONFIG

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
  rule <k> (_._`(_`)(oenv((C:Id :: Env:Map) Oenv:List), F:Id, Vl:List{Val})) ~> K:K 
           =>
           invoke(_`(_`)(F:Id, Vl)) </k>
       <class> C1:Id => C:Id </class>
       <obj> Oenv1:List => (C :: Env) Oenv </obj>
       <env> Env1:Map => . </env>
       <fstack> .List => [ C1, Env1, (restore(Oenv1)~>K) ] <_/fstack>
  rule <k> super_`(_`)(F, Vl) ~> K => invoke(_`(_`)(F:Id, Vl)) </k>
       <class> C => C1 </class>
       <env> Env1 => . </env>
       <fstack> .List => [ C, Env1, K ] <_/fstack>
       <pgm_>
            <classes_>
                   <className> C </className>
                   <extends> C1 </extends>
            <_/classes>
       <_/pgm>

  rule <k> invoke(_`(_`)(F:Id, Vl))
           =>
           (_`(_`)(function(sNat getloc( [C, F], ( @global :: GEnv:Map ))), Vl))
       <_/k>
       <class> C </class>
       <genv> GEnv </genv>
       if getloc( [C, F], ( @global :: GEnv )) =/=Bool null 
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
       if getloc( [C, F], ( @global :: GEnv )) ==Bool null 

--- method call: function value loading 
--- <OO modified>: the global environment not longer included in the loacl function call environment
---                    because the global variables are noe data members in the object class
  rule <k> (_`(_`)(function(L),Vl:List{Val})) => S:Stmt~>return(0); </k> 
       <env> _ => .Map[N..N+Nat|Xl| / getList{K}(Xl:List{Id})] </env>
       <genv> GEnv </genv>
       <store_> L:Nat |-> lambda(Xl,S) (. => N:Nat..N+Nat|Xl| |-> getList{K}(Vl)) <_/store>
       <nextLoc> N => N +Nat |Xl| </nextLoc>

--- returning from a method call
  rule <k> return(V:Val); ~> _ => V ~> K </k>
       <fstack> [ C, Env, K ] => . <_/fstack>
       <class> _ => C </class>
       <env> _ => Env </env>

---</SKOOL modified>
endkm

------------------------------
--- instruction processing ---
------------------------------
kmod SKOOL-UNTYPED-INSTR-PROCESSING is including SKOOL-UNTYPED-CONFIG 

  rule {} => .
  rule <k> {Ss:Stmts} => Ss~>env(Env) <_/k> <env> Env:Map </env> 
  rule S1:Stmt S2:Stmt => S1~>S2 

---<SKOOL modified> 
  rule <k> _=_;(X:Id, V:Val) => . <_/k> 
       <env> Env:Map </env>
       <genv> GEnv:Map </genv>
       <obj_> (C:Id :: Env1:Map) Oenv:List </obj>
       <class> C </class>
       <store> Store:Map => Store [ V / getloc(X, ((@local :: Env) ((C :: Env1) Oenv)(@global :: GEnv))) ] </store>
---</SKOOL modified>

 --- for array assignment, first evaluate the array and its index
  context _[[HOLE]]=_;
  context [HOLE][_]=_;
  rule <k> array(L:Nat,_)[N:Nat]=V; => . <_/k>
       <store> Sigma:Map => Sigma[V/(L +Int N)] </store> 

  rule V; => . 
  rule if true then S:Stmt else _ => S:Stmt
  rule if false then _ else S => S 
  rule <k> while B:Exp do S  => if B then {S while B do S} else {} <_/k>
  rule <k> write(I:Int); => . <_/k> <out_> . => ListItem(I) </out>
endkm

-----------------
--- semantics ---
-----------------
kmod SKOOL-UNTYPED-SEMANTICS is 
  including SKOOL-UNTYPED-PREPROCESSING +
            SKOOL-UNTYPED-FUNCTION-CALL +
            SKOOL-UNTYPED-EXPR-EVALUATION +
            SKOOL-UNTYPED-INSTR-PROCESSING
endkm


