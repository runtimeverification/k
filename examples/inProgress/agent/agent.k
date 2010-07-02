in ../../../k-prelude
in agent-syntax
in agent-programs

kmod GENERIC-SUBSTITUTION is including BOUNDING-EXP-SYNTAX + PL-INT + K
---beta-substitution definition using the K AST visitor pattern
---assuming the binding operator is _._
  syntax K ::= Exp | BoundingExp
             | K [ K / Id ] [prec 0]
             | beta List{K} [ K / Id ] 
               [prec 0 latex "{#1}\sqbracket{{#2}/_\beta{#3}}"]
             | beta-beta K [ K / Id ]  
               [prec 0 strict(1) latex "{#1}\sqbracket{{#2}/_\beta^0{#3}}"]
             | clearDone K [strict latex "{\it unbox}({#1})"]
  syntax KResult ::= done List{K}  [latex "\framebox{${#1}$}"]
  syntax Id ::= fresh Nat  --- to generate fresh names
  syntax CellLabel ::= nextId

  --- "boxed" versions of the K constructors (all of them are strict)
  syntax K ::= K box(~>) K [latex "{#1}\framebox{$\kra$}{#2}" strict]
             | K box(,,) K [latex "{#1}\framebox{$,\!\!,$}{#2}" strict]
  syntax KLabel ::= box ( KLabel ) [latex "\framebox{#1}"]
  context box(Label:KLabel)(_,,`[HOLE`]:K,,_)

  rule K'[K:K/Y:Id] => clearDone(beta K'[K/Y]) [structural]
  rule clearDone(done(K)) => K [structural] 

  rule beta Y[K/Y] => done(K) [structural]  ---this does the actual substitution
  rule <k> beta '_._(X:Id,,K':K)[K/Y] => 
           box('_._)(done(fresh(N)) box(,,) beta-beta beta K'[fresh(N)/X][K/Y])
      <_/k> <nextId>N:Nat => sNat N</nextId>
---    if Y =/=Bool X [structural] ---renaming bound variables
  rule beta-beta done(K')[K/Y] => beta K'[K/Y] [structural]
---  rule <k> beta '_._(Y,,K':K)[K/Y] => done('_._(Y,,K':K)) <_/k> [structural]
  rule beta .[K/Y] => done(.) [structural]
  rule beta((K1:K ~> K2:K))[K/Y] => beta K1[K/Y] box(~>) beta K2[K/Y]
    if K1 =/=Bool . andBool K2 =/=Bool . [structural]
  rule beta .List{K}[K/Y] => done(.List{K}) [structural]
  rule beta (K1,,K2,,Kl)[K/Y] 
    => beta K1[K/Y] box(,,) beta (K2,,Kl)[K/Y] [structural]
  rule beta Label(Kl)[K/Y] => box(Label)(beta Kl[K/Y])
    if Label =/=Bool '_._ andBool Label(Kl) =/=Bool Y  [structural]

  rule box(Label)(done(Kl:List`{K`})) => done(Label(Kl)) [structural]
  rule done(Kl) box(,,) done(Kl':List`{K`}) => done((Kl,,Kl')) [structural]
  rule done(K1) box(~>) done(K2) => done((K1 ~> K2)) [structural]
endkm

kmod AGENT-SEMANTICS is including AGENT-SYNTAX + GENERIC-SUBSTITUTION
  syntax Val ::= Bool | Int | nothing | lambda BoundingExp | Id
  syntax Exp ::= Val
  syntax KResult ::= Val

  configuration
    <T>
      <agents>
        <agent*> 
          <threads>
            <thread*>
              <k>.K</k>
              <nextId>0</nextId>
              <holds>.Map</holds>
            </thread*>
          </threads>
          <busy>.Set</busy>
          <me>0</me>
          <parent>-1</parent>
        </agent*>
      </agents>
      <nextAgent>1</nextAgent>
      <world>SetItem(0)</world>
      <barrier>true</barrier>
      <waiting>.Set</waiting>
      <messages>
        <message*>
          <from>.K</from>
          <to>.Set</to>
          <body>.K</body>
        </message*>
      </messages>
      <I/O>
        <in>.List</in>
        <out>.List</out>
      </I/O>
    </T>

--- Basic arithmetic operations; integers are converted to reals when needed
--- NOTE: add more here
  rule  I1:Int + I2:Int => I1 +Int I2  
--- following rules for _*_ need to be written like that because of 
--- parsing ambiguities: a*b can also be seen as __(a,*b) ...
  rule  _*_(I1,I2) => I1 *Int I2 
  rule  I1 / I2 => I1 /Int I2  if I2 =/=Bool 0 
  rule  I1 <= I2 => I1 <=Int I2  
  rule  V1:Val == V2:Val => V1 ==Bool V2
  rule  not T:Bool => notBool T
  rule  true and E:Exp => E
  rule  false and E => false

--- Basic statement constructs
  rule  skip => nothing [structural]
  rule  (V:Val ;  S2:Exp) => S2  [structural]
  rule  if true then S1:Exp else S2 => S1
  rule  if false then S1 else S2 => S2
  rule <k>while E do S => if E then S ; while E do S else skip<_/k> [structural]

--- I/O
   rule <k>read => I:Int<_/k> <in>ListItem(I) => .<_/in>
   rule <k>print V => nothing <_/k> <out_>. => ListItem(V)</out>

--- Callcc
  syntax Val ::= cc ( K ) [latex "{\it cc}({#1})"]
  rule <k>(callcc(V) => (V cc(K:K))) ~> K</k> 
  rule <k> (cc(K) V)~> _ => V ~> K</k> 

--- Threads:Nat
   rule <thread_> <k>spawn S:Exp => nothing<_/k> <nextId>N</nextId> <_/thread>
        (. => <thread_> <k>S</k> <nextId>N</nextId> <_/thread>)
   rule (<thread_> <k>V</k> <holds>Holds:Map</holds> <_/thread> => .)
        <busy>Busy:Set => Busy -Set keys(Holds)</busy>
   rule <k>acquire V => nothing<_/k> <holds_>. => V|->0<_/holds> 
        <busy>Busy (.=>SetItem(V))</busy>
     if notBool(V in Busy)
   rule <k>acquire V => nothing<_/k> <holds_>V|->(N:Nat => sNat N)<_/holds>
   rule <k>release V => nothing<_/k> <holds_>V|->(sNat N => N)<_/holds>
   rule <k>release V => nothing<_/k> <holds_>V|->0 => .<_/holds> 
        <busy_>SetItem(V)=> .<_/busy>
   rule <k>rendezvous V => nothing<_/k> <k>rendezvous V => nothing<_/k>

--- Agents
  rule <agent_> <k>newAgent S => N2:Nat<_/k> <nextId>N</nextId> <me>N1:Nat</me> 
       <_/agent> <world_>. => SetItem(N2)<_/world>
       (. => <agent_><me>N2</me><parent>N1</parent><k>S</k><nextId>N</nextId><_/agent>) <nextAgent>N2 => sNat N2</nextAgent>
  rule  (<agent_><threads>.Bag</threads> <me>N</me> <_/agent>=> .) <world_>SetItem(N) => .<_/world>
  rule <k>me => N<_/k> <me>N</me>
  rule <k>parent => N<_/k> <parent>N</parent>
  rule <me>N1</me> <k>send V to N2 => .<_/k>
       (. => <message> <from>N1</from> <to>SetItem(N2)</to> <body>V</body> </message>)
  rule <me>N</me> <k>receive=>V<_/k> 
       <message_> <to_>SetItem(N)=>.<_/to> <body>V</body> <_/message>
  rule <message> <from>N2</from> <to_>SetItem(N1) => .<_/to> <body>V</body> 
       </message> <me>N1</me> <k>receiveFrom N2 => V<_/k>
  rule <me>N</me> <k>broadcast V => .<_/k> <world>W:Set</world>
       (. => <message> <from>N</from> <to>W</to> <body>V</body> </message>)
  rule <message_><to>.Set</to><_/message> => . [structural]
  rule <agent_> <me>N1</me> <k>sendSynch V to N2 => .<_/k> <_/agent>
       <agent_><me>N2</me> <k>receiveFrom N1 => V<_/k> <_/agent>
  rule <k>sendSynch V to N2 => .<_/k> 
       <agent_><me>N2</me> <k>receive => V<_/k> <_/agent>
  rule <me>N</me> <threads> <thread_><k>barrier<_/k> <_/thread> </threads> 
       <barrier>true</barrier> <waiting>W (. => SetItem(N))</waiting> 
    if notBool(N in W)
  rule <barrier>true=>false</barrier> <waiting>W</waiting> <world>W</world> 
    if W =/=Bool .
  rule <me>N</me> <k>barrier => .<_/k> <barrier>false</barrier>
       <waiting_>SetItem(N) => .<_/waiting>
  rule <barrier>false => true</barrier> <waiting>.Set</waiting>

--- Abrupt termination (of thread, of agent, of system)
  rule <k>haltThread~>_ => nothing</k> 
  rule <threads_> <k>haltAgent<_/k> <_/threads> => <threads>.Bag</threads>
  rule <agents_><k>haltSystem<_/k><_/agents> => <agents>.Bag</agents>


---Function application (through beta-substitution)
  rule <k> '__('lambda_('_._(X:Id,,E)),,E':Exp) => E[E' / X]<_/k>

---Fix point operator (through beta-substitution)
  rule <k> 'mu_('_._(X,,E)) => E['mu_('_._(X,,E)) / X]<_/k>

endkm

kmod AGENT is including AGENT-SEMANTICS + AGENT-PROGRAMS 
  syntax Bag ::= run ( KLabel ) | run ( KLabel , List{K} )
  rule run(KL:KLabel) => run(KL,.List{K}) [structural]
  rule run(KL,L:List{K}) => <T_> <k>KL(.List{K})</k> <in>List(L)</in> <_/T> [structural]
endkm
