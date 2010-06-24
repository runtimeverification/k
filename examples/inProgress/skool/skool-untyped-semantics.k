--- in skool-untyped-syntax


--------------------------------------
--- SKOOL-UNTYPED-SEMANTICS module ---
--------------------------------------


kmod SKOOL-UNTYPED-SEMANTICS is including SKOOL-UNTYPED-DESUGARED-SYNTAX + K 


  syntax Val ::= Int | Bool | Object
  syntax Exp ::= Val
  syntax Object ::= oenv ( List )

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
                     <nextLoc> 0 </nextLoc>
                     <obj> .List </obj>
                     <class> main </class>
                     <pgm>
                           <classes*>
                                    <className> object </className>
                                    <extends> object </extends>
                                    <fields> .K </fields>
                                    <methods> .K </methods>
                           </classes*>
                     </pgm>
                </T>

--- <OO stuff modified>
---  rule <k> X:Id => V:Val <_/k>  
---       <env_> X |-> L:Nat <_/env>
---       <store_> L |-> V <_/store> 

--- getloc: returns the "location" of an object X 
    syntax Nat ::= null | getloc ( Id , List ) [strict]
---  syntax Loc ::= Nat | null | getloc ( Id , List ) [strict] --- does not work because of the sanity check
  macro getloc(X, ( ( C |-> .) Oenv )) = getloc(X, Oenv )
  macro getloc(X, ( ( C |-> ( Y:Id |-> L:Nat Env )) Oenv ))
        =
        if X ==Bool Y then L else getloc(X,  ((C |->  Env )Oenv)) fi
  macro getloc(X, .) = null

  syntax Id ::= @ny   --- the name of the current environment for an object
  rule <k> X:Id => Store(getloc(X, ((@ny |-> Env) (C |-> Env1) Oenv))) <_/k>
       <env> Env:Map </env>
       <obj_> (C:Id |-> Env1:Map) Oenv:List </obj>
       <class> C </class>
       <store> Store:Map </store>  
  rule <k> this =>  oenv((C |-> Env1) Oenv) <_/k>
       <obj_> (C |-> Env1) Oenv </obj>

--- </OO stuf modified>

  rule <k> ++X => I:Int +Int 1 <_/k>
       <env_> X |-> L <_/env>
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

--- array value:
---    first arg. is the location of the first element in the array, and 
---    the second arg. is the array size
  syntax Val ::= array ( Nat , Nat )  

  rule <k> array(L,_)[N:Nat] => Sigma(L +Int N) <_/k> <store> Sigma </store> .
                                --- untyped SIMPLE does not check array bounds

  rule (sizeOf(array(_,N)) => N) 
  rule <k> var X ; => .K <_/k> 
       <env> Env:Map => Env[L / X] </env> 
       <store_> .Map => L |-> 0 <_/store>
       <nextLoc> L => sNat(L) </nextLoc> 
  
--- If an array is declared, then calculate its size; 
---    then next rule gives its semantics
  context var X[[HOLE]];
  rule <k> var X[N]; => . <_/k> 
       <env> Env => Env[L/X] </env>
       <store_>. => L |-> array(sNat L, N) <_/store>
       <nextLoc> L => sNat L +Nat N </nextLoc> 

  rule {} => .
  rule <k> {Ss:Stmts} => Ss~>env(Env) <_/k> <env> Env </env> 
  rule S1:Stmt S2:Stmt => S1~>S2 

--- <OO stuf modified>
  rule <k> _=_;(X, V:Val) => . <_/k> 
       <env> Env:Map </env>
       <obj_> (C |-> Env1:Map) Oenv:List </obj>
       <class> C </class>
       <store> Store => Store [ V / getloc(X, ((@ny |-> Env) (C |-> Env1) Oenv)) ] </store>
--- </OO stuf modified>

 --- for array assignment, first evaluate the array and its index
  context _[[HOLE]]=_;
  context [HOLE][_]=_;
  rule <k> array(L,_)[N]=V; => . <_/k>
       <store> Sigma:Map => Sigma[V/(L +Int N)] </store> 

  rule V; => . 
  rule if true then S:Stmt else _ => S 
  rule if false then _ else S => S 
  rule <k> while B:Exp do S  => if B then {S while B do S} else {} <_/k>

--- function value; like arrays, functions also evaluate to 
---    their address (wrapped as a specific value)
  syntax Val ::= function( Nat )

--- actual function values are stored as lambda abstractions
  syntax Val ::= lambda ( List{Id} , Stmt )

---<OO stuff modified (in fact are repalced by method call rules)
---  op function : Nat -> Val   
  rule <k> method F:Id(Xl:List{Id}) S => . <_/k> 
       <env> Env => Env[L/F] </env> 
       <nextLoc> L => L +Nat 2 </nextLoc> 
       <store_>(.Map => L |-> function(sNat L) sNat(L) |-> lambda(Xl,S))<_/store>


--- the next is used to stack the environment and the computation at each function call
  syntax ListItem ::=  ( Map , K )

  rule <k> _`(_`)(function(L),Vl:List`{Val`})~>K => S~>return(0); </k> 
       <fstack> .List => (Env,K) <_/fstack>
       <env> Env => GEnv:Map[N..N+Nat|Xl| / getList{K}(Xl)] </env>
       <genv> GEnv </genv>
       <store_> L |-> lambda(Xl,S) (. => N..N+Nat|Xl| |-> getList{K}(Vl)) <_/store>
       <nextLoc> N => N +Nat |Xl| </nextLoc>


---  rule <k> return(V); ~> _ => V ~> K </k>
---       <fstack> (Env,K) => . <_/fstack>
---       <env> _ => Env </env>

--- </OO stuff modified>

  rule <k> read() => I <_/k> <in> ListItem(I) => . <_/in>
  rule <k> write(I); => . <_/k> <out_> . => ListItem(I) </out>


---<OO stuff modified: the next rule is replaced by the last rule from the definition of kpgm label
--- when we are done with the first pass (computation and genv are empty),
---   call main and initialize the global environment
---  rule <k> . => main(); </k> <env> Env </env> <genv> . => Env </genv>
---</OO stuff modified>


-----------------------
---<OO stuff added> ---
-----------------------

  syntax ListItem ::= Id |-> Map
  syntax KLabel ::= create | invoke | addOEnvLayer 
  syntax K ::= restore ( List ) | discard

--- new operator
---   the semantics of the new operator consists of two actions: memory allocation for the new object
---   and the execution of the statements included in the constructor
----  the current class, environment and object are stored on the stack
  syntax ListItem ::=  [ Id , Map , K ]
  rule <k> (new_`(_`)(C:Id, Vl))~>K => create(C)~>invoke(_`(_`)(C, Vl))</k>
       <env> Env => . </env>
       <obj> Oenv:List => . </obj>
       <class> C1:Id => C </class>
       <fstack> . => [ C1, Env, (discard ~> this ~> restore(Oenv)~>K) ] <_/fstack>
       if C =/=Bool main
  rule <k> (new_`(_`)(C:Id, Vl))~>K => create(C)~>invoke(_`(_`)(C, Vl))</k>
       <env> Env => . </env>
       <obj> Oenv:List => . </obj>
       <class> C1:Id => C </class>
       <fstack> . => [ C1, Env, . ] <_/fstack>
       if C ==Bool main

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


  rule <k> create(object) => oenv(Oenv (object |-> .Map)) <_/k>
       <obj> Oenv => Oenv (object |-> .Map) </obj>

--- add a new tagged environment layer to the  current object
  rule <k> addOEnvLayer(C) => . <_/k>
       <env> Env => . </env>
       <obj_> . => (C |-> Env) </obj>

--- method call
--- the internal name of a method is a pair [class, method-name], in order to be unique
--- (we assume that the name of a class in a program is unique)

  rule <k> (_._`(_`)(oenv((C |-> Env) Oenv), F, Vl)) ~> K => oenv((C |-> Env) Oenv) ~> invoke(_`(_`)(F:Id, Vl)) </k>
       <class> C1 => C </class>
       <obj> Oenv1:List => (C |-> Env) Oenv </obj>
       <env> Env1 => . </env>
       <fstack> .List => [ C1, Env1, (restore(Oenv1)~>K) ] <_/fstack>
  rule <k> super_`(_`)(F, Vl) ~> K => oenv(Oenv) ~> invoke(_`(_`)(F:Id, Vl)) </k>
       <class> C => C1 </class>
       <obj> Oenv1 (C |-> Env) Oenv => Oenv </obj>
       <env> Env1 => . </env>
       <fstack> .List => [ C1, Env1, (restore((C |-> Env) Oenv)~>K) ] <_/fstack>
       <pgm_>
            <classes_>
                   <className> C </className>
                   <extends> C1 </extends>
            <_/classes>
       <_/pgm>


  syntax Id ::= [ Id , Id ]
  rule <k> oenv((C |-> Env) Oenv) ~> invoke(_`(_`)(F:Id, Vl))
           =>
           oenv((C |-> Env) Oenv) ~>(_`(_`)(function(sNat getloc( [C, F], ( @ny |-> GEnv ))), Vl)) <_/k>
       <genv> GEnv </genv>
       if getloc( [C, F], ( @ny |-> GEnv )) =/=Bool null 
  rule <k> oenv((C |-> Env) Oenv) ~> invoke(_`(_`)(F:Id, Vl))
           =>
           oenv(Oenv) ~>invoke(_`(_`)(F:Id, Vl)) <_/k>
       <class> C => C1 </class>
       <pgm_>
            <classes_>
                   <className> C </className>
                   <extends> C1 </extends>
            <_/classes>
       <_/pgm>

       <genv> GEnv </genv>
       if getloc( [C, F], ( @ny |-> GEnv )) ==Bool null 


  rule <k> oenv((C |-> Env) Oenv) ~>(_`(_`)(function(L),Vl:List`{Val`}))~>K => S~>return(0); </k> 
       <env> Env1 => GEnv:Map[N..N+Nat|Xl| / getList{K}(Xl)] </env>
       <genv> GEnv </genv>
       <store_> L |-> lambda(Xl,S) (. => N..N+Nat|Xl| |-> getList{K}(Vl)) <_/store>
       <nextLoc> N => N +Nat |Xl| </nextLoc>

  rule <k> return(V); ~> _ => V ~> K </k>
       <fstack> [ C, Env, K ] => . <_/fstack>
       <class> _ => C </class>
       <env> _ => Env </env>

  rule <k> V ~> discard => . <_/k>     --- discards the value (item?) from the top of the computation

  rule <k> V ~> restore(Oenv) => V <_/k> 
       <obj> _ => Oenv </obj>

  rule <k> _`(_`)(F, Xl) => _._`(_`)(this, F, Xl) <_/k>

  rule <k> _instanceOf_(oenv( (C |-> Env) Oenv), C1) => true <_/k> if (C ==Bool C1)
  rule <k> _instanceOf_(oenv( (C |-> Env) Oenv), C1) => _instanceOf_(oenv(Oenv), C1) <_/k> if (C =/=Bool C1) 
  rule <k> _instanceOf_( oenv(.), C1) => false <_/k>
  


----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------
--- List{Val}
  syntax List{Val} ::= Val |  List{Val} , List{Val} [ditto]
  syntax List{Exp} ::= List{Val}

--- length
  syntax Nat ::= `| List{Id} `|
  macro |.List{Id}| = 0  
  macro |X,Xl| = sNat |Xl|

--- generate sequence of locations
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..N2:Nat => N1,,sNat N1..N2 [structural]

--- environment recovery
  syntax K ::= env ( Map ) 
  rule env(_) ~> env(Env) => env(Env) [structural] 
  rule <k> env(Env) => . <_/k> <env> _ => Env </env> [structural] 
  rule <k> V ~> (env(Env) => .) <_/k> <env> _ => Env </env> [structural]

endkm


