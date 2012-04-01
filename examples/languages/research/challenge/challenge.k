in challenge-syntax

module CHALLENGE imports CHALLENGE-SYNTAX 
  syntax Val ::= Bool | Int | Float 
  syntax Exp ::= Val
  syntax KResult ::= Val


  configuration
    <T>
      <agents>
        <agent multiplicity="*" color="red"> 
          <threads>
            <thread multiplicity="*">
              <k>$PGM:K</k>
              <env>.Map</env>
              <fstack>.List</fstack>
              <holds>.Map</holds>
            </thread>
          </threads>
          <aspect>{}</aspect>
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
        <in stream="stdin">.List</in>
        <out stream="stdout">.List</out>
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
  rule  I1 / I2 => I1 /Int I2  when I2 =/=Int 0 
  rule  I1 / F2 => Int2Float(I1) /Float F2  when F2 =/=Float 0.0 
  rule  F1 / I2 => F1 /Float Int2Float(I2)  when I2 =/=Int 0 
  rule  F1 / F2 => F1 /Float F2  when F2 =/=Float 0.0 
  rule  I1 <= I2 => I1 <=Int I2  
  rule  I1 <= F2 => Int2Float(I1) <=Float F2  
  rule  F1 <= I2 => F1 <=Float Int2Float(I2)  
  rule  F1 <= F2 => F1 <=Float F2
  rule  V1:Val == V2:Val => V1 ==K V2
  rule  not T:Bool => notBool T
  rule  true and E:Exp => E
  rule  false and E => false

--- Variable declaration
  rule <k>var X:Id,Xs:Ids; => var Xs; ...</k> 
       <env>Env => Env[N / X]</env>
       <store>... . => N |-> 0 ...</store> 
       <nextLoc>N:Nat => N +Int 1</nextLoc>
  rule <k> var; => . ...</k>

--- Variable lookup
  rule <k>X:Id=>K:K ...</k> <env>X|->N ...</env> <store>N|->K ...</store>

--- Variable assignment
  rule <k>X=V:Val;=>. ...</k> <env>X|->N ...</env> <store>N|->(_=>V) ...</store>

--- Variable increment
  rule <k>++X => I:Int +Int 1 ...</k> <env>X|->N ...</env> <store>N|->(I=>I+Int 1) ...</store>

--- Basic statement constructs
  rule  {} => . [structural]
  rule <k>{S:Stmt} => S~>env(Env) ...</k> <env>Env</env>
  rule  S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule  V; => .
  rule  if true then S1 else S2 => S1
  rule  if false then S1 else S2 => S2
  rule <k>while E do S => if E then S while E do S else {} ...</k> [structural]

--- I/O
   rule <k>read=>I ...</k> <in>ListItem(I)=>. ...</in>
   rule <k>print V; => . ...</k> <out>... .=>ListItem(V)</out>

--- Memory allocation and pointers
  rule <k>&X => N ...</k> <env>X|->N ...</env>
  rule <k>*N => V ...</k> <store>N|->V ...</store>
  rule <k>malloc(N1:Nat) => N2:Nat ...</k> <ptr>. => N2|->N1 ...</ptr>
       <store>. => (N2..N1 +Int N2 |-> 0) ...</store> <nextLoc>N2 => N1 +Int N2</nextLoc>
  rule <k>free(N2); => . ...</k> <ptr>N2|->N1 => . ...</ptr>
       <store>Store:Map => Store[undef/N2..N1 +Int N2]</store>
  context *HOLE=_;
  rule <k>*N=V; => . ...</k> <store>N|->(_=>V) ...</store>

--- Lists
  rule V:[Vs:Vals] => [V,Vs]
  rule head [V,Vs] => V
  rule tail [V,Vs] => [Vs]
  define 'isVal([Vs:Vals]) => true

--- Aspects
  rule <k>aspect S => . ...</k> <aspect>_=>S</aspect>

--- Functions
  syntax Val ::= closure-lambda ( Ids , Stmt , Map ) [latex "{\it closure}_\lambda({#1},{#2},{#3})"]
  rule <k>lambda Xs.S1 => closure-lambda(Xs,(S2 S1),Env) ...</k> <env>Env:Map</env> <aspect>S2</aspect>
  syntax K ::= "frame" "(" K "," Map ")"
  rule <k> _`(_`)(closure-lambda(Xs,S,Env),Vs) ~> K 
        => bindto(Xs,Vs) ~> S return 0;</k>
       <env> Env':Map => Env </env> 
       <fstack> . => ListItem(frame(K,Env')) ...</fstack>

  syntax K ::= "bindto" "(" Ids "," Vals ")"
  rule <k> bindto((X,Xs => Xs),(V,Vs:Vals => Vs)) ...</k>
       <env> Env => Env[N/X] </env>
       <store>... . => N |-> V ...</store>
       <nextLoc> N => N +Int 1 </nextLoc>
  rule <k> bindto(.Ids,.Exps) => . ...</k>  [:structural:]

  rule <k>return V;~>_ => V~>K</k> 
       <env>_=>Env</env> 
       <fstack>ListItem(frame(K,Env)) => . ...</fstack>

--- Callcc
  syntax Val ::= cc ( K , Map , List ) [latex "{\it cc}({#1},{#2},{#3})"]
  rule <k>(callcc(V) => _`(_`)(V, cc(K,Env,FStack))) ~> K</k> <env>Env</env> <fstack>FStack:List</fstack>
  rule <k> _`(_`)(cc(K,Env,FStack),V)~>_ => V~>K</k> <env>_=>Env</env> <fstack>_=>FStack</fstack>

--- Sequential non-determinism
  rule <k>randomBool=>true ...</k>
  rule <k>randomBool=>false ...</k>

--- Threads
   rule <thread>...  <k>spawn S => . ...</k> <env>Env</env>  ...</thread>
        (. => <thread>...  <k>S</k> <env>Env</env>  ...</thread>)
   rule (<thread>...  <k>.K</k> <fstack>.List</fstack> <holds>Holds:Map</holds>  ...</thread> => .)
        <busy>Busy:Set => Busy -Set keys(Holds)</busy>
   rule <k>acquire V; => . ...</k> <holds>... . => V|->0 ...</holds> <busy>Busy (.=>SetItem(V))</busy>
     when notBool(V in Busy) [transition] 
   rule <k>acquire V; => . ...</k> <holds>... V|->(N => N +Int 1) ...</holds> [transition]
   rule <k>release V; => . ...</k> <holds>... V|->(N => N -Int 1) ...</holds>
   when (N >Int 0)
   rule <k>release V; => . ...</k> <holds>... V|->0 => . ...</holds> <busy>... SetItem(V)=>. ...</busy>
   rule <k>rendezvous V; => . ...</k> <k>rendezvous V; => . ...</k> [transition]

--- Agents
  rule <agent>...  <k>newAgent S => N2 ...</k> <me>N1</me>  ...</agent> <world>... . => SetItem(N2) ...</world>
       (. => <agent>... <me>N2</me><parent>N1</parent><k>S</k> ...</agent>) <nextAgent>N2 => N2 +Int 1</nextAgent>
  rule  (<agent>... <threads>.Bag</threads> <me>N</me>  ...</agent>=> .) <world>... SetItem(N) => . ...</world>
  rule <k>me => N ...</k> <me>N</me>
  rule <k>parent => N ...</k> <parent>N</parent>
  rule <me>N1</me> <k>send V to N2; => . ...</k>
       (. => <message> <from>N1</from> <to>SetItem(N2)</to> <body>V</body> </message>)
  rule <me>N</me> <k>receive=>V ...</k> <message>...  <to>... SetItem(N)=>. ...</to> <body>V</body>  ...</message> [transition]
  rule <me>N1</me> <k>receiveFrom N2 => V ...</k>
       <message> <from>N2</from> <to>... SetItem(N1) => . ...</to> <body>V</body> </message> [transition]
  rule <me>N</me> <k>broadcast V; => . ...</k> <world>W:Set</world>
       (. => <message> <from>N</from> <to>W</to> <body>V</body> </message>)
  rule <message>... <to>.Set</to> ...</message> => . [structural]
  rule <agent>...  <me>N1</me> <k>sendSynch V to N2; => . ...</k>  ...</agent>
       <agent>... <me>N2</me> <k>receiveFrom N1 => V ...</k>  ...</agent> [transition]
  rule <k>sendSynch V to N2; => . ...</k> <agent>... <me>N2</me> <k>receive => V ...</k>  ...</agent> [transition]
  rule <me>N</me> <threads> <thread>... <k>barrier; ...</k>  ...</thread> </threads> <barrier>true</barrier>
       <waiting>W (. => SetItem(N))</waiting> when notBool(N in W) [transition]
  rule <barrier>true=>false</barrier> <waiting>W</waiting> <world>W</world> when W =/=Set .
  rule <me>N</me> <k>barrier; => . ...</k> <barrier>false</barrier> <waiting>... SetItem(N)=>. ...</waiting>
  rule <barrier>false => true</barrier> <waiting>.Set</waiting>

--- Abrupt termination (of thread, of agent, of system)
  rule <k>haltThread;~>_ => .</k> <fstack>_=>.List</fstack>  [transition]
  rule <threads>...  <k>haltAgent; ...</k>  ...</threads> => <threads>.Bag</threads> [transition]
  rule <agents>... <k>haltSystem; ...</k> ...</agents>=> <agents>.Bag</agents> [transition]

--- Code generation (via reflection)
  syntax KLabel ::= quoteit[ Nat ] [latex "{\it quote}_{\scriptstyle{#1}}"]
                  | box ( KLabel ) [latex "\framebox{#1}"]
  syntax Val ::= code ( List{K} ) [latex "{\it code}({#1})"]
  syntax K ::= K box(~>) K [latex "{#1}\framebox{$\kra$}{#2}" strict]
             | K box(,,) K [latex "{#1}\framebox{,,}{#2}" strict]

  context box(Label:KLabel)(_,,HOLE,,_)

---  op 'quote_  : -> KLabel[metadata "generated label"]
---  op 'unquote_ : -> KLabel[metadata "generated label"]

  rule <k>quote E => quoteit[0](E) ...</k>
  rule quoteit[N](quote(E)) => box('quote_)(quoteit[N +Int 1](E))
  rule quoteit[0](unquote(E)) => E
  rule quoteit[N](unquote(E)) => box('unquote_)(quoteit[N -Int 1](E))
  when (N >Int 0)
  rule quoteit[N](.) => code(.) [structural]
  rule quoteit[N]((K1:K ~> K2:K)) => quoteit[N](K1) box(~>) quoteit[N](K2)
    when K1 =/=K . andBool K2 =/=K .
  rule code(K1) box(~>) code(K2) => code((K1 ~> K2))
  rule quoteit[N](Label(Kl:List`{K`})) => box(Label)(quoteit[N](Kl))
    when Label(.List{K}) =/=K 'quote_(.List{K}) andBool Label(.List{K}) =/=K 'unquote_(.List{K})
  rule box(Label)(code(Kl)) => code(Label(Kl))
  rule quoteit[N](.List{K}) => code(.List{K})
  rule quoteit[N]((Kl1:List`{K`},, Kl2:List`{K`})) => quoteit[N](Kl1) box(,,) quoteit[N](Kl2)
    when Kl1 =/=List{K} .List{K} andBool Kl2 =/=List{K} .List{K}
  rule code(Kl1) box(,,) code(Kl2) => code((Kl1,, Kl2))
  rule lift V => code(V)
  rule eval code(K) => K

----------------------------------------------
--- Auxilliary declarations and operations ---
----------------------------------------------
--- environment recovery
  syntax K ::= env ( Map )
  rule env(_)~>env(Env) => env(Env) [structural]
  rule <k>env(Env)=>. ...</k> <env>_=>Env</env> [structural]
  rule V ~> env(Env) => env(Env) ~> V [structural]

--- generate sequence of locations
  syntax List{K} ::= Nat .. Nat
  rule N1..N1 => .List{K} [structural anywhere]
  rule N1..N2 => N1,,(N1 +Int 1)..N2 [structural anywhere]


--- List{Val}
  syntax Vals ::= List{Val,","} 
end module








--- Fixed point
--- mu has been desugared in the syntax module, so it does not need to be defined
--- However, below there are several possibilities to define it in case one does
--- not want to desugar it but define it directly
---(
---mu as in call-by-name
  syntax K ::= closure-mu ( Exp , Map )
  rule <k>mu X . E => closure-mu(E, Env[N / X])</k> <env>Env</env>
       <store>. => N |-> closure-mu(E, Env[N / X]) ...</store> <nextLoc>N => N +Int 1</nextLoc>
  rule <k>closure-mu(E, Env) => E ~> env(Env') ...</k> <env>Env':Map => Env</env>
---)

---(
---mu through assigment (if X does not appear at top of E)
  rule <k>mu X.E => var X; ~> X=E; ~> X ~> env(Env) ...</k> <env>Env</env>
---)

---(
---mu just for functions
   context mu_.HOLE 
   rule <k>mu X.closure-lambda(Y,S,Env) => closure-lambda(Y,S,Env[N/X]) ...</k>
        <store>. => N|->closure-lambda(Y,S,Env[N/X]) ...</store> <nextLoc>N => N +Int 1</nextLoc>
---)

