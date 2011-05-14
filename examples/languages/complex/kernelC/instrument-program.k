kmod INSTRUMENT-PROGRAM is including KERNELC-BASIC-SEMANTICS
  syntax Event ::=  write ( Nat : Nat <- Int ) | read ( Nat : Nat |-> Int ) | spwn ( Nat : Nat ) | acq ( Nat : Nat ) | rel ( Nat : Nat ) 
  syntax PreEvent ::= rea ( Nat : Nat ) | spw ( Nat )
  syntax Builtins ::= Event
  syntax K ::= PreEvent | Event | Bool
  configuration <k> .K </k> <id> 0 </id> <event> false </event> <trace> .List </trace>

  rule <k> * N:Nat = V:Int ~> (. => write(T: N <- V)) <_/k> 
       <id> T:Nat </id>
       <event> false => true </event> 
       [structural]

  rule <k> * N  ~> (. => rea(T: N)) <_/k> 
       <id> T </id>
       <event> false => true </event> 
       [structural]

  rule <k> V ~> (rea(T: N) => read(T: N |-> V)) <_/k> [structural]

  rule <k> spawn E:Exp  ~> (. => spw(T)) <_/k> 
       <id> T </id>
       <event> false => true </event> 
       [structural]

  rule <k> N ~> (spw(T) => spwn(T: N)) <_/k>

  rule <k> acquire(N)  ~> (. => acq(T: N)) <_/k> 
       <id> T </id>
       <event> false => true </event> 
       [structural]

  rule <k> release(N)  ~> (. => rel(T: N)) <_/k> 
       <id> T </id>
       <event> false => true </event> 
       [structural]

  rule <k> _:Val ~> (Event:Event => .) <_/k> 
       <event> true => false </event> 
       <trace_> . => ListItem(Event) </trace>
       [structural]
endkm


kmod FSM-MONITOR is
  configuration <fsm> <fsm-state> init </fsm-state> <fsm-counter> 0 </fsm-counter> <fsm-events> .List </fsm-events> <fsm-transitions> .Map </fsm-transitions>

  syntax FsmState ::= init | stuck
  syntax StateEvent ::= FsmState `|`| K
  
  rule <fsm-state> S:FsmState => S' </fsm-state> <fsm-events> E:K <_/fsm-events>
       <fsm-transitions_> S || E |-> S':FsmState <_/fsm-transitions>
  [structural]

  rule <fsm-state> S => stuck </fsm-state> <fsm-events> E:K <_/fsm-events>
       <fsm-transitions> M:Map </fsm-transitions>
  if S || E in keys(M) ==Bool false [structural]
endkm
