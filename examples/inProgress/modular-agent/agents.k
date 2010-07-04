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