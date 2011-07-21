
in challenge-syntax
in challenge-programs

kmod CHALLENGE-SEMANTICS is including CHALLENGE-DESUGARED-SYNTAX + K + #CONVERSION 
  syntax Val ::= Bool | Int | Float
  syntax Exp ::= Val
  syntax K ::= List{Exp} | Stmt
  syntax KResult ::= List{Val}

  configuration
    <T>
      <agents>
        <agent multiplicity="*" color="red"> 
          <threads>
            <thread multiplicity="*">
              <k>.K</k>
              <env>.Map</env>
              <fstack>.List</fstack>
              <holds>.Map</holds>
            </thread>
          </threads>
          <aspect>.K</aspect>
          <busy>.Set</busy>
          <store>.Map</store>
          <nextLoc>0</nextLoc>
          <ptr>.Map</ptr>
          <me>0</me>
          <parent>-1</parent>
        </agent>
      </agents>
      <nextAgent>1</nextAgent>
      <world>SetItem(0)</world>
      <barrier>true</barrier>
      <waiting>.Set</waiting>
      <messages>
        <message multiplicity="*">
          <from>.K</from>
          <to>.Set</to>
          <body>.K</body>
        </message>
      </messages>
      <IO>
        <in>.List</in>
        <out>.List</out>
      </IO>
    </T>

--- Basic arithmetic operations; integers are converted to reals when needed
--- NOTE: add more here
  rule  I1:Int + I2:Int => I1 +Int I2  
  rule  I1 + F2:Float => Int2Float(I1) +Float F2 
  rule  F1:Float + I2 => F1 +Float Int2Float(I2) 
  rule  F1 + F2 => F1 +Float F2 
--- following rules for _*_ need to be written like that because of parsing ambiguities: a*b can also be seen as __(a,*b) ...
  rule  _*_(I1,I2) => I1 *Int I2 
  rule  _*_(I1,F2) => Int2Float(I1) *Float F2  
  rule  _*_(F1,I2) => F1 *Float Int2Float(I2)  
  rule  _*_(F1,F2) => F1 *Float F2  
  rule  I1 / I2 => I1 /Int I2  if I2 =/=Bool 0 
  rule  I1 / F2 => Int2Float(I1) /Float F2  if F2 =/=Bool 0.0 
  rule  F1 / I2 => F1 /Float Int2Float(I2)  if I2 =/=Bool 0 
  rule  F1 / F2 => F1 /Float F2  if F2 =/=Bool 0.0 
  rule  I1 <= I2 => I1 <=Int I2  
  rule  I1 <= F2 => Int2Float(I1) <=Float F2  
  rule  F1 <= I2 => F1 <=Float Int2Float(I2)  
  rule  F1 <= F2 => F1 <=Float F2
  rule  V1:Val == V2:Val => V1 ==Bool V2
  rule  not T:Bool => notBool T
  rule  true and E:Exp => E
  rule  false and E => false

--- Variable declaration
  rule <k>var Xl:List{Id}; => .<_/k> <env>Env => Env[N..N+Nat|Xl| / getList{K}(Xl)]</env>
       <store_>. => N..N+Nat|Xl| |-> 0<_/store> <nextLoc>N:Nat => N +Nat |Xl|</nextLoc>

--- Variable lookup
  rule <k>X:Id=>K:K<_/k> <env>X|->N<_/env> <store>N|->K<_/store>

--- Variable assignment
  rule <k>X=V:Val;=>.<_/k> <env>X|->N<_/env> <store>N|->(_=>V)<_/store>

--- Variable increment
  rule <k>++X => I:Int +Int 1<_/k> <env>X|->N<_/env> <store>N|->(I=>I+Int 1)<_/store>

--- Basic statement constructs
  rule  {} => . [structural]
  rule <k>{S:Stmt} => S~>env(Env)<_/k> <env>Env</env>
  rule  S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule  V; => .
  rule  if true then S1 else S2 => S1
  rule  if false then S1 else S2 => S2
  rule <k>while E do S => if E then S while E do S else {}<_/k> [structural]

--- I/O
   rule <k>read=>I<_/k> <in>ListItem(I)=>.<_/in>
   rule <k>print V; => .<_/k> <out_>.=>ListItem(V)</out>

--- Memory allocation and pointers
  rule <k>&X => N<_/k> <env>X|->N<_/env>
  rule <k>*N => V<_/k> <store>N|->V<_/store>
  rule <k>malloc(N1:Nat) => N2:Nat<_/k> <ptr>. => N2|->N1<_/ptr>
       <store>. => N2..N1 +Nat N2 |-> 0<_/store> <nextLoc>N2 => N1 +Nat N2</nextLoc>
  rule <k>free(N2); => .<_/k> <ptr>N2|->N1 => .<_/ptr>
       <store>Store:Map => Store[undef/N2..N1 +Nat N2]</store>
  context *[HOLE]=_;
  rule <k>*N=V; => .<_/k> <store>N|->(_=>V)<_/store>

--- Lists
  rule V:[Vl:List{Val}] => [V,Vl]
  rule head [V,Vl] => V
  rule tail [V,Vl] => [Vl]

--- Aspects
  rule <k>aspect S => .<_/k> <aspect>_=>S</aspect>

--- Functions
  syntax Val ::= closure-lambda ( List{Id} , Stmt , Map ) [latex "{\it closure}_\lambda({#1},{#2},{#3})"]
  rule <k>lambda Xl.S1 => closure-lambda(Xl,(S2 S1),Env)<_/k> <env>Env:Map</env> <aspect>S2</aspect>
  syntax ListItem ::= ( K , Map )
  rule <k> _`(_`)(closure-lambda(Xl,S,Env),Vl) ~> K => S return 0;</k>
       <env>Env':Map => Env[N..N+Nat|Xl|/getList{K}(Xl)]</env> <fstack>.=>(K,Env')<_/fstack>
       <store>.=> N..N+Nat|Xl| |-> getList{K}(Vl)<_/store> <nextLoc>N => N +Nat |Xl|</nextLoc>
  rule <k>return V;~>_ => V~>K</k> <env>_=>Env</env> <fstack>(K,Env)=>.<_/fstack>

--- Callcc
  syntax Val ::= cc ( K , Map , List ) [latex "{\it cc}({#1},{#2},{#3})"]
  rule <k>(callcc(V) => _`(_`)(V, cc(K,Env,FStack))) ~> K</k> <env>Env</env> <fstack>FStack:List</fstack>
  rule <k> _`(_`)(cc(K,Env,FStack),V)~>_ => V~>K</k> <env>_=>Env</env> <fstack>_=>FStack</fstack>

--- Sequential non-determinism
  rule <k>randomBool=>true<_/k>
  rule <k>randomBool=>false<_/k>

--- Threads
   rule <thread_> <k>spawn S => .<_/k> <env>Env</env> <_/thread>
        (. => <thread_> <k>S</k> <env>Env</env> <_/thread>)
   rule (<thread_> <k>.K</k> <fstack>.List</fstack> <holds>Holds:Map</holds> <_/thread> => .)
        <busy>Busy:Set => Busy -Set keys(Holds)</busy>
   rule <k>acquire V; => .<_/k> <holds_>. => V|->0<_/holds> <busy>Busy (.=>SetItem(V))</busy>
     if notBool(V in Busy)
   rule <k>acquire V; => .<_/k> <holds_>V|->(N => sNat N)<_/holds>
   rule <k>release V; => .<_/k> <holds_>V|->(sNat N => N)<_/holds>
   rule <k>release V; => .<_/k> <holds_>V|->0 => .<_/holds> <busy_>SetItem(V)=>.<_/busy>
   rule <k>rendezvous V; => .<_/k> <k>rendezvous V; => .<_/k>

--- Agents
  rule <agent_> <k>newAgent S => N2<_/k> <me>N1</me> <_/agent> <world_>. => SetItem(N2)<_/world>
       (. => <agent_><me>N2</me><parent>N1</parent><k>S</k><_/agent>) <nextAgent>N2 => sNat N2</nextAgent>
  rule  (<agent_><threads>.Bag</threads> <me>N</me> <_/agent>=> .) <world_>SetItem(N) => .<_/world>
  rule <k>me => N<_/k> <me>N</me>
  rule <k>parent => N<_/k> <parent>N</parent>
  rule <me>N1</me> <k>send V to N2; => .<_/k>
       (. => <message> <from>N1</from> <to>SetItem(N2)</to> <body>V</body> </message>)
  rule <me>N</me> <k>receive=>V<_/k> <message_> <to_>SetItem(N)=>.<_/to> <body>V</body> <_/message>
  rule <me>N1</me> <k>receiveFrom N2 => V<_/k>
       <message> <from>N2</from> <to_>SetItem(N1) => .<_/to> <body>V</body> </message>
  rule <me>N</me> <k>broadcast V; => .<_/k> <world>W:Set</world>
       (. => <message> <from>N</from> <to>W</to> <body>V</body> </message>)
  rule <message_><to>.Set</to><_/message> => . [structural]
  rule <agent_> <me>N1</me> <k>sendSynch V to N2; => .<_/k> <_/agent>
       <agent_><me>N2</me> <k>receiveFrom N1 => V<_/k> <_/agent>
  rule <k>sendSynch V to N2; => .<_/k> <agent_><me>N2</me> <k>receive => V<_/k> <_/agent>
  rule <me>N</me> <threads> <thread_><k>barrier;<_/k> <_/thread> </threads> <barrier>true</barrier>
       <waiting>W (. => SetItem(N))</waiting> if notBool(N in W)
  rule <barrier>true=>false</barrier> <waiting>W</waiting> <world>W</world> if W =/=Bool .
  rule <me>N</me> <k>barrier; => .<_/k> <barrier>false</barrier> <waiting_>SetItem(N)=>.<_/waiting>
  rule <barrier>false => true</barrier> <waiting>.Set</waiting>

--- Abrupt termination (of thread, of agent, of system)
  rule <k>haltThread;~>_ => .</k> <fstack>_=>.List</fstack>
  rule <threads_> <k>haltAgent;<_/k> <_/threads> => <threads>.Bag</threads>
  rule <agents_><k>haltSystem;<_/k><_/agents>=> <agents>.Bag</agents>

--- Code generation (via reflection)
  syntax KLabel ::= quoteit[ Nat ] [latex "{\it quote}_{\scriptstyle{#1}}"]
                  | box ( KLabel ) [latex "\framebox{#1}"]
  syntax Val ::= code ( List{K} ) [latex "{\it code}({#1})"]
  syntax K ::= K box(~>) K [latex "{#1}\framebox{$\kra$}{#2}" strict]
             | K box(,,) K [latex "{#1}\framebox{,,}{#2}" strict]

  context box(Label:KLabel)(_,,`[HOLE`]:K,,_)

---  op 'quote_  : -> KLabel[metadata "generated label"]
---  op 'unquote_ : -> KLabel[metadata "generated label"]

  rule <k>quote E => quoteit[0](E)<_/k>
  rule quoteit[N](quote(E)) => box('quote_)(quoteit[sNat(N)](E))
  rule quoteit[0](unquote(E)) => E
  rule quoteit[sNat(N)](unquote(E)) => box('unquote_)(quoteit[N](E))
  rule quoteit[N](.) => code(.) [structural]
  rule quoteit[N]((K1:K ~> K2:K)) => quoteit[N](K1) box(~>) quoteit[N](K2)
    if K1 =/=Bool . andBool K2 =/=Bool .
  rule code(K1) box(~>) code(K2) => code((K1 ~> K2))
  rule quoteit[N](Label(Kl:List`{K`})) => box(Label)(quoteit[N](Kl))
    if Label =/=Bool 'quote_ andBool Label =/=Bool 'unquote_
  rule box(Label)(code(Kl)) => code(Label(Kl))
  rule quoteit[N](.List{K}) => code(.List{K})
  rule quoteit[N]((Kl1:List`{K`},, Kl2:List`{K`})) => quoteit[N](Kl1) box(,,) quoteit[N](Kl2)
    if Kl1 =/=Bool .List{K} andBool Kl2 =/=Bool .List{K}
  rule code(Kl1) box(,,) code(Kl2) => code((Kl1,, Kl2))
  rule lift V => code(V)
  rule eval code(K) => K

----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------
--- environment recovery
  syntax K ::= env ( Map )
  rule env(_)~>env(Env) => env(Env) [structural]
  rule <k>env(Env)=>.<_/k> <env>_=>Env</env> [structural]
  rule V ~> env(Env) => env(Env) ~> V [structural]

--- List{Val}
  syntax List{Val} ::= Val | List{Val} , List{Val} [ditto]
  syntax List{Exp} ::= List{Val}

--- length
  syntax Nat ::= `| List{Id} `|
  rule |()| => 0 [structural]
  rule |X,Xl| => sNat|Xl| [structural]

--- generate sequence of locations
  syntax List{K} ::= Nat .. Nat
  rule N1..N1 => .List{K} [structural]
  rule N1..N2 => N1,,sNat N1..N2 [structural]
endkm

kmod CHALLENGE is including CHALLENGE-SEMANTICS + CHALLENGE-PROGRAMS 
  syntax Bag ::= run ( KLabel ) | run ( KLabel , List{K} )
  rule run(KL:KLabel) => run(KL,.List{K}) [structural]
  rule run(KL,L:List{K}) => <T_> <k>KL(.List{K})</k> <in>List(L)</in> <_/T> [structural]
endkm







--- Fixed point
--- mu has been desugared in the syntax module, so it does not need to be defined
--- However, below there are several possibilities to define it in case one does
--- not want to desugar it but define it directly
---(
---mu as in call-by-name
  syntax K ::= closure-mu ( Exp , Map )
  rule <k>mu X . E => closure-mu(E, Env[N / X])</k> <env>Env</env>
       <store>. => N |-> closure-mu(E, Env[N / X])<_/store> <nextLoc>N => sNat N</nextLoc>
  rule <k>closure-mu(E, Env) => E ~> env(Env')<_/k> <env>Env':Map => Env</env>
---)

---(
---mu through assigment (if X does not appear at top of E)
  rule <k>mu X.E => var X; ~> X=E; ~> X ~> env(Env)<_/k> <env>Env</env>
---)

---(
---mu just for functions
   context mu_.[HOLE] 
   rule <k>mu X.closure-lambda(Y,S,Env) => closure-lambda(Y,S,Env[N/X])<_/k>
        <store>. => N|->closure-lambda(Y,S,Env[N/X])<_/store> <nextLoc>N => sNat N</nextLoc>
---)

