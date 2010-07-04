load ../../../k-prelude
load ../substitution/substitution

kmod BASIC-RUN is  including K
  configuration <T> <k> .K </k> </T>
  op run : KLabel -> Bag
  macro run(KL:KLabel) = <T_> <k>KL(.List{K})</k> <_/T>
endkm

kmod EXP is including PL-INT + K
--- Basic arithmetic and boolean operations;
  syntax K ::= K + K   [gather(E e) prec 33 strict]       --- addition
             | K * K   [gather(E e) prec 31 strict]       --- multiplication
             | K / K   [gather(E e) prec 31 strict]       --- division
             | K <= K  [prec 37 latex "{#1}\leq{#2}" seqstrict]
             | K == K  [prec 37 strict]                   --- equality test
             | not K     [prec 53 strict]                   --- boolean negation
             | K and K [gather(E e) prec 55 strict(1)]    --- boolean conjunction
             | if K then K else K   [strict(1)]
  syntax KResult ::= Bool | Int 

  rule  I1:Int + I2:Int => I1 +Int I2  
--- following rules for _*_ need to be written like that because of 
--- parsing ambiguities: a*b can also be seen as __(a,*b) ...
  rule  _*_(I1,I2) => I1 *Int I2 
  rule  I1 / I2 => I1 /Int I2  if I2 =/=Bool 0 
  rule  I1 <= I2 => I1 <=Int I2  
  rule  V1:KResult == V2:KResult => V1 ==Bool V2
  rule  not T:Bool => notBool T
  rule  true and E:K => E
  rule  false and E => false
  rule if true then E else _ => E
  rule if false then _ else E => E
endkm

kmod EXP-PROGRAMS is including EXP
  op p1 : -> K
  macro p1 = 3 + 5
endkm

kmod EXP-RUN is including EXP-PROGRAMS + BASIC-RUN endkm


kmod FUN is including SUBSTITUTION
  syntax K ::= lambda Id . K [latex "\lambda{#1}.{#2}"]
             | K K  [strict]
             | mu Id . K [latex "\mu{#1}.{#2}"]

  syntax KResult ::= Id 
                   | aLambda K [latex "\lambda{#1}"]
  syntax K ::= aMu K [latex "\mu{#1}"]

  macro lambda X:Id . E:K = aLambda([X]E)
  macro mu X . E = aMu([X]E)
---Function application (through beta-substitution)
  rule <k> aLambda([X]E) E':K => E[E' / X]<_/k>

---Fix point operator (through beta-substitution)
  rule <k> aMu ([X]E) => E[aMu ([X]E) / X]<_/k>
endkm


kmod IDS is  including PL-ID 
  ops a f x y z : -> Id
endkm

kmod FUN-PROGRAMS is including FUN + EXP + IDS
  op p2 : -> K
  macro p2 = lambda x . x

  op p3 : -> K 
  macro p3 = x mu f . lambda x . (f x)

  op p4 : -> K
  macro p4 = a ((lambda z . (z z)) lambda x.lambda y.(x y))

  op p5 : -> K
  macro p5 = a ((lambda x.lambda y.(x y)) y)

  op p6 : -> K
  macro p6 = ((lambda x . x + 7) 10)
  
  op p7 : -> K
  macro p7 = ((lambda x . if 5 <= 3 then x + 7 else 0) y)

  op p8 : -> K 
  macro p8 = ((mu f . (lambda x . if x <= 0 then 1 else ((f (x + -1)) * x))) 5)
endkm

kmod FUN-RUN is including BASIC-RUN + FUN-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
endkm

kmod CONTROL is including FUN
  syntax K ::= callcc K [prec 50 strict]
             | halt K [strict]

  syntax KResult ::= cc ( K ) [latex "{\it cc}({#1})"]
  rule [save-cxt] : <k>(callcc(V:KResult) => (V cc(K:K))) ~> K</k> 
  rule [restore-cxt] : <k> (cc(K) V)~> _ => V ~> K</k> 
  rule <k>halt(V)~>_ => V</k> 
endkm


kmod CONTROL-PROGRAMS is including CONTROL + FUN + EXP + IDS
  ops k return : -> Id 

  op p9 : -> K 
  macro p9 = ((mu f . (lambda x . lambda y . if x <= 0 then halt(y) else ((f (x + -1)) (y * x)))) 5) 1
  
  op p10 : -> K 
  macro p10 = callcc (lambda k . 7)

  op p11 : -> K 
  macro p11 = callcc (lambda k . (k 7))

  op p12 : -> K 
  macro p12 = callcc (lambda k . ((k 7) + 5))

--- using callcc for returning
  op p13 : -> K 
  macro p13 = ((lambda f . (callcc (f -5)))( lambda x . (lambda return . ((lambda x . (0 / 0)) (
          if (0 <= x)
          then (return 0)
          else (return 1)
        ))))) + 3
---
endkm

kmod CONTROL-RUN is including BASIC-RUN + CONTROL-PROGRAMS 
  configuration <T> <k> .K </k> <nextId> 0 </nextId> </T>
endkm

kmod IO is including K + PL-INT
  configuration <k> .K </k>  
                <in> .List </in> <out> .List </out>
  syntax K ::= Int
             | read
             | print K [strict]
  
   rule <k>read => I:Int<_/k> <in>ListItem(I) => .<_/in>
   rule <k>print V:KResult => V <_/k> <out_>. => ListItem(V)</out>
endkm

kmod IO-PROGRAMS is including IO + FUN + EXP + IDS
  op p14 : -> K
  macro p14 = print(read)

  op p15 : -> K 
  macro p15 = print((mu f . (lambda x . if print(x) * x <= 0 then 1 else ((f read) * x))) read)
endkm

kmod IO-RUN is including IO-PROGRAMS + BASIC-RUN
  configuration <T> <k> .K </k>  <nextId> 0 </nextId>
                <in> .List </in> <out> .List </out> </T>
  syntax Bag ::= run ( KLabel , List{K} )
  macro run(KL:KLabel,L:List`{K`}) 
      = <T_> <k> KL(.List{K}) </k> <in>List(L)</in> <_/T>
endkm

kmod REF is including K
  configuration <k> .K </k>  
                <mem> .Map </mem> <nextLoc> 0 </nextLoc>
  
  syntax K ::= Nat
             | ref K [strict]
             | * K [strict]
             | K := K [strict(2)]

  context * [HOLE] := _
  rule <k> ref V:KResult => N:Nat <_/k> 
       <mem_> . => N |-> V <_/mem> <nextLoc> N => sNat N </nextLoc>
  rule <k> * N => V <_/k> <mem_> N |-> V <_/mem>
  rule <k> * N := V => N <_/k> <mem_> N |-> (_ => V) <_/mem>
endkm

kmod IMP is including EXP
  syntax K ::= K ; K                  [prec 100 gather(e E) strict(1)]
             | while K do K
  syntax KResult ::= skip
  
  rule V:KResult ; S:K => S
  rule <k> while E:K do S => if E then (S ; while E do S) else skip <_/k>
endkm

kmod IMP-PROGRAMS is  including IMP + REF + FUN + IDS
  op p16 : -> K 
  macro p16 = ((lambda x.(lambda y.((while(2<=*y) do (
          (*x:= _*_(*x,*y));
          (*y:=(*y+-1))
       )); *x))) (ref 1)) (ref 5) 
endkm

kmod IMP-RUN is including IMP-PROGRAMS + BASIC-RUN
  configuration <T> <k> .K </k>  <nextId> 0 </nextId>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc> </T>
endkm

kmod THREADS is including IMP
  configuration <threads> <thread*> 
                  <k> .K </k> <holds> .Map </holds>
                </thread*> </threads>
                <busy> .Set </busy>
  syntax K ::= spawn K       [prec 90]
             | acquire K     [strict]
             | release K     [strict]
             | rendezvous K  [strict]

  rule [spawn-thread] : <thread_> <k>spawn S:K => skip<_/k> <_/thread>
       (. => <thread_> <k>S</k> <_/thread>)

  rule [end-thread] : (<thread_> <k>V:KResult</k> <holds>Holds:Map</holds> <_/thread> => .)
       <busy>Busy:Set => Busy -Set keys(Holds)</busy>
  rule [free-acquire] : <k>acquire V => skip<_/k> <holds_>. => V|->0<_/holds> 
       <busy>Busy (.=>SetItem(V))</busy>
    if notBool(V in Busy)
  rule [reentrant-acquire] : <k>acquire V => skip<_/k> <holds_>V|->(N:Nat => sNat N)<_/holds>
  rule [reentrant-release] : <k>release V => skip<_/k> <holds_>V|->(sNat N => N)<_/holds>
  rule [release] : <k>release V => skip<_/k> <holds_>(V|->0 => .)<_/holds> 
       <busy_>(SetItem(V)=> .)<_/busy>
  rule [rendezvous] : <k>rendezvous V => skip<_/k> <k>rendezvous V => skip<_/k>  

endkm

kmod THREADS-PROGRAMS is including THREADS + REF + IO + FUN + CONTROL + IDS
  op p17 : -> K
  macro p17 = ((lambda x . lambda y . (
           (spawn(*x:=0));
           ((while(1<=*x) do (*y:=*y+1)) ;
           print(*y))
           )) (ref 1)) (ref 0)
        
  op p18 : -> K
  macro p18 =  (lambda x . ( 
                (spawn ((rendezvous 1) ; (print(*x)) ; (rendezvous 2))) ;
                (spawn ((rendezvous 3) ; (print(*x)) ; (rendezvous 4))) ;
                (print(*x)) ;
                (*x := *x + 1) ;
                (rendezvous 1) ;  (rendezvous 2) ;
                (*x := *x + 1) ;
                (rendezvous 3) ; (rendezvous 4))) (ref 1)
   

  op p19 : -> K
  macro p19 = (lambda x . ( 
                (spawn ((*x:= *x + 1) ; (rendezvous 1) ));
                (*x := *x + 1) ;
                (rendezvous 1) ;
                (print(*x)))) (ref 1)
    
  op p20 : -> K
  macro p20 = (lambda x . ( 
                (spawn ((acquire(x)) ; (*x:= *x + 1) ; (release(x)) ; (rendezvous 1) ));
                (acquire(x)) ;
                (*x := *x + 1) ;
                (release(x)) ;
                (rendezvous 1) ;
                (print(*x)))) (ref 1)
    
  op p21 : -> K
  macro p21 = (lambda x . ( 
                (spawn ((acquire(x)) ; (rendezvous 1) ; (*x:= *x + 1) ; (halt(0)) ));
                (rendezvous 1) ;
                (acquire(x)) ;
                (*x := *x + 1) ;
                (release(x)) ;
                (print(*x)))) (ref 1)
endkm

kmod THREADS-RUN is including BASIC-RUN + THREADS-PROGRAMS
  configuration <T> <threads> <thread*> 
                  <k> .K </k> <nextId> 0 </nextId> <holds> .Map </holds>
                </thread*> </threads>
                <in> .List </in> <out> .List </out>
                <mem> .Map </mem> <nextLoc> 0 </nextLoc>
                <busy> .Set </busy> </T>
endkm

kmod AGENTS is  including IMP
  configuration
      <agent*> 
          <me>0</me>
          <parent>-1</parent>
          <control> <k> .K </k> </control>
          <ready> true </ready>
      </agent*>
      <nextAgent>1</nextAgent>
      <world>SetItem(0)</world>
      <barrier>true</barrier> <waiting>.Set</waiting>
      <messages> <message*>
          <from>.K</from> <to>.Set</to> <body>.K</body>
      </message*> </messages>
  syntax K ::= newAgent K
             | me
             | parent
             | receive
             | receiveFrom K     [strict]
  syntax K ::= send K to K       [strict]
             | sendSynch K to K  [strict]
             | barrier        
             | broadcast K       [strict]
             | haltAgent


--- Agents
  rule [agent-creation] : <agent_> <k>newAgent S:K => N2:Nat<_/k> <me>N1:Nat</me> 
       <_/agent> <world_>. => SetItem(N2)<_/world>
       (. => <agent_><me>N2</me><parent>N1</parent><k>S</k><_/agent>) 
       <nextAgent>N2 => sNat N2</nextAgent>
  rule [agent-completion] : (<agent_><control>.Bag</control> <me>N:Nat</me> <_/agent>=> .) 
       <world_>(SetItem(N) => .)<_/world>
  rule [halt-agent] : <control_> <k>haltAgent<_/k> <_/control> => <control> .Bag </control> .
  rule <k>me => N<_/k> <me>N</me>
  rule <k>parent => N<_/k> <parent>N</parent>
  rule <me>N1</me> <k>send V to N2 => skip<_/k> <ready>true</ready>
       (. => <message> <from>N1</from> <to>SetItem(N2)</to> <body>V</body> 
             </message>)
  rule <me>N</me> <k>receive=>V:KResult<_/k> <ready>true</ready> 
       <message_> <to_>SetItem(N)=>.<_/to> <body>V</body> <_/message>
  rule <message> <from>N2</from> <to_>SetItem(N1) => .<_/to> <body>V</body> 
       </message> <me>N1</me> <k>receiveFrom N2 => V<_/k> <ready>true</ready>
  rule <me>N</me> <k>broadcast V => skip<_/k> <ready>true</ready> 
       <world>W:Set</world>
       (. => <message> <from>N</from> <to>W</to> <body>V</body> </message>)
  rule <message_><to>.Set</to><_/message> => . [structural]
  rule <agent_> <me>N1</me> <k>sendSynch V to N2 => skip<_/k> <ready>true</ready> <_/agent>
       <agent_><me>N2</me> <k>receiveFrom N1 => V<_/k> <ready>true</ready> <_/agent>
  rule <k>sendSynch V to N2 => skip<_/k> <ready>true</ready> 
       <agent_><me>N2</me> <k>receive => V<_/k> <ready>true</ready> <_/agent>
  rule [start-waiting-at-barrier] : <me>N</me> <k>barrier<_/k> <ready>true => false</ready> 
       <barrier>true</barrier> <waiting>W (. => SetItem(N))</waiting> 
  rule [lifting-barrier] : <barrier>true=>false</barrier> <waiting>W</waiting> <world>W</world> 
    if W =/=Bool .
  rule [leave-barrier] : <me>N</me> <k>barrier => skip<_/k> <ready>false => true</ready> <barrier>false</barrier>
       <waiting_>(SetItem(N) => .)<_/waiting>
  rule [lowering-barrier] : <barrier>false => true</barrier> <waiting>.Set</waiting>
endkm


kmod AGENTS-PROGRAMS is including AGENTS + THREADS + IO + FUN + IDS
  op p22 : -> K
  macro p22 = ((lambda y . lambda z . (send z to y))
          (newAgent(((lambda y . (sendSynch me to y)) (receiveFrom parent)) ; 
                    (spawn haltAgent) ; (print(receive))))) 
           (newAgent(((lambda z . ((send 17 to z) ; (print(z)))) receive)))
endkm


kmod AGENTS-RUN is including AGENTS-PROGRAMS + BASIC-RUN
  configuration
    <T>
      <agent*> 
          <control>
              <thread*>
                  <k>.K</k>
                  <nextId>0</nextId>
                  <holds>.Map</holds>
              </thread*>
          </control>
          <busy>.Set</busy>
          <me>0</me>
          <parent>-1</parent>
          <ready>true</ready>
      </agent*>
      <nextAgent>1</nextAgent>
      <world>SetItem(0)</world>
      <barrier>true</barrier> <waiting>.Set</waiting>
      <messages> <message*>
          <from>.K</from> <to>.Set</to> <body>.K</body>
      </message*> </messages>
      <I/O> <in>.List</in> <out>.List</out> </I/O>
    </T>
endkm

kmod MODULAR-AGENT is including AGENTS-RUN
endkm

