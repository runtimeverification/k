in ../../../../k-prelude.maude
in simple-typed-dynamic-syntax
in ../simple-typed-programs

kmod SIMPLE-TYPED-DYNAMIC-SEMANTICS is including SIMPLE-TYPED-DYNAMIC-DESUGARED-SYNTAX + K 

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
               --- (wrapped as a specific "function" value together with the function type)
               --- and the address contains the actual function body (as an untyped "lambda" value")
               | function ( Type , Nat )
               | lambda ( List{Id} , Stmt ) [latex "\lambda{#1}.{#2}"]

--- the values are expressions
  syntax Exp ::= Val 


-------------------------------------
--- Computations "swallow" syntax ---
-------------------------------------

--- We have to subsort all the syntactic categories to K, and the lists of values
--- to KResult.  Recall that the second argument of a function application is a list
--- of expressions, so that becomes a result when it becomes a list of values
  syntax K ::= Stmts | List{Exp} | List{IdType} | List{Type}
  syntax KResult ::= List{Val}


---------------------
--- Configuration ---
---------------------

  configuration <T>
                     <k> K:K </k>
                     <fstack> .List </fstack>
                     <env> .Map </env>
                     <genv> .Map </genv>
                     <store> .Map </store>
                     <in> .List </in>
                     <out> .List </out>
                     <return> none </return>    --- this cell holds the expecter return type
                     <nextLoc> 0 </nextLoc>
                </T>


--------------------
--- Declarations ---
--------------------

--- Variable declaration
  rule <k> var X:Id : Tp:Type ; => .K <_/k>
       <env> Env:Map => Env[L:Nat / X] </env>
       <store_> . => L |-> initVal(Tp) <_/store>     --- intialized with default value for its type
       <nextLoc> L => sNat(L) </nextLoc>

--- Array declaration
  context var X[[HOLE]] : Tp[];
  rule <k> var X[N:Nat] : Tp[]; => .K <_/k>
       <env> Env => Env[L/X] </env>
       <store_> . => L |-> array(_`[`](Tp), sNat L, N) <_/store>
       <nextLoc> L => sNat L +Nat N </nextLoc>

  rule <k> function F:Id(XTl:List{IdType}) : Tp S:Stmt => .K <_/k>
       <env> Env => Env[L / F] </env>
       <nextLoc> L => L +Nat 2 </nextLoc> 
       <store_>(.Map => L |-> function(typeList(XTl) -> Tp,sNat L) sNat(L) |-> lambda(idList(XTl), S))<_/store> 

--- when we are done with the first pass (computation and genv are empty), call main and initialize the global environment
  rule <k> .K => main(); </k>
       <env> Env </env>
       <genv> .Map => Env </genv> 

--- expressions evaluation

  rule <k> X:Id => V:Val <_/k>
       <env_> X |-> L:Nat <_/env>
       <store_> L:Nat |-> V <_/store> 
  rule <k> ++ X => I:Int +Int 1 <_/k>
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
  --- array component
  rule <k> array(_,L,M:Nat)[N:Nat] => Sigma(L +Int N) <_/k>
       <store> Sigma:Map </store> 
       if N >=Nat 0 andBool N <=Nat M 
  rule sizeOf(array(_,_,N)) => N 
  rule <k> read() => I <_/k>
       <in> ListItem(I) => .List <_/in> 

--- function call processing
 rule <k> _`(_`)(function(Tpl:List`{Type`} -> Tp:Type, L:Nat),Vl:List{Val})  ~> K:K
          =>
          S:Stmt ~> return(initVal(Tp));
      </k>
      <fstack> .List => (Env:Map,K,Tp') <_/fstack>
      <env> Env =>  GEnv[| Xl:List{Id} | from N / getList{K}(Xl)] </env>
      <genv> GEnv:Map </genv>
      <return> Tp':Type => Tp </return>
      <store_> L |-> lambda(Xl, S) (.Map => | Xl | from N |-> getList{K}(Vl)) <_/store>
      <nextLoc> N:Nat => N +Nat | Xl | </nextLoc> 
      if typeOf(Vl) ==Bool Tpl 

  rule <k> return(V:Val); ~> _ => V ~> K </k>
       <fstack> (Env,K,Tp') => .List <_/fstack>
       <env> _ => Env </env>
       <return> Tp => Tp' </return>
       if typeOf(V) ==Bool Tp

--- instructions processing
  rule {} => .K 
  rule <k> {Ss:Stmts} => Ss ~> env(Env) <_/k>
       <env> Env:Map </env> 
  rule S1:Stmt S2:Stmt => S1 ~> S2 
  rule <k> X:Id = V2:Val ; => .K <_/k>
       <env_> X |-> L:Nat <_/env>
       <store_> L |-> (V1:Val => V2) <_/store>
       if typeOf(V1) ==Bool typeOf(V2) 

  context _[[HOLE]] = _ ; 
  context [HOLE][_] = _ ; 
  rule <k> array(_`[`](Tp:Type),L,M:Nat)[N:Nat] = V:Val ; => .K <_/k>
       <store> Sigma:Map => Sigma[V / (L +Int N)] </store> 
       if N >=Nat 0 andBool N <=Nat M andBool typeOf(V) ==Bool Tp 
  rule V ; => .K 
  rule if true then S:Stmt else _ => S 
  rule if false then _ else S => S 
  rule <k> while B:Exp do S  => if B then {S while B do S} else {} <_/k> 
  rule <k> write(I:Int) ; => .K <_/k>
       <out_> .List => ListItem(I) </out>  


----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------
  syntax Val ::=
                 initVal ( Type )
               | none
  macro initVal(int) = 0
  macro initVal(bool) = false
  macro initVal(void) = none
  macro initVal(_`[`](Tp:Type)) = array(_`[`](Tp),0,0)

  syntax List{Type} ::= typeOf ( List{Val} )  
  macro typeOf(function(Tp, _)) = Tp 
  macro typeOf(array(Tp,_,_)) = Tp 
  macro typeOf(I:Int) = int 
  macro typeOf(T:Bool) = bool 
  macro typeOf(none) = void 
  macro typeOf(V1:Val,V2:Val,Vl:List{Val}) = typeOf(V1),typeOf(V2,Vl) 
  macro typeOf(.List{Bottom}) = .List{Bottom} 


--- List{Val}
  syntax List{Val} ::= Val | List{Bottom} 
                     | List{Val} , List{Val} [ditto]

  syntax List{Exp} ::= List{Val}  

--- translation of a list of typed names into a list of the corresponding untyped names
  syntax List{Id} ::= idList ( List{IdType} ) 
  macro idList(.List{Bottom}) = .List{Bottom} 
  macro idList(X:Id : Tp:Type, XTl:List`{IdType`}) = X, idList(XTl) 

--- translation of a lists of typed names into a list of the corresponding types
  syntax List{Type} ::= typeList ( List{IdType} ) 
  macro typeList(.List{Bottom}) = .List{Bottom} 
  macro typeList(X : Tp, XTl) = Tp,typeList(XTl) 

--- length
  syntax Nat ::= `| List{Id} `|
  macro |.List{Bottom}| = 0  
  macro |X:Id,Xl:List{Id}| = sNat |Xl|

--- from
  syntax List{K} ::= Nat from Nat 
  macro 0 from N1:Nat = .List{K} 
  macro sNat N2:Nat from N1 = N1,,(N2 from sNat N1)

--- environment recovery
  syntax K ::= env ( Map ) 
  rule (env(_) ~> env(Env:Map) => env(Env)) [structural] 
  rule <k> (env(Env) => .K) <_/k>
      <env> (_ => Env) </env> [structural] 
  rule <k> V:Val ~> (env(Env) => .K) <_/k>
       <env> (_ => Env) </env> [structural] 

--- the following is nedeed for stacking
 syntax ListItem ::=  ( Map , K , Type )  
endkm

kmod SIMPLE-TYPED-DYNAMIC is 
  including SIMPLE-TYPED-DYNAMIC-SEMANTICS 
  including SIMPLE-TYPED-PROGRAMS 
  syntax Bag ::= run ( KLabel ) 
  macro run(PgmName:KLabel) =
          <T_> 
             <k> PgmName(.List{K}) </k>
             <in> List(7,,23,,654,,656,,54,,456,,436345647643567,,354654364356,,4357643576) </in>
          <_/T> 
endkm



