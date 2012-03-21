require seq

module AGENTS imports SEQ
  configuration
      <agent multiplicity="*"> 
          <me>0</me>
          <parent>-1</parent>
          <control> <k color="green"> .K </k> </control>
      </agent> 
      @latex("\\kBR")
      <nextAgent>1</nextAgent>
      <world>SetItem(0)</world>
      <barrier>true</barrier> <waiting>.Set</waiting> 
      @latex("\\kBR")
      <messages> <message multiplicity="*">
          <from>.K</from> <to>.Set</to> <body>.K</body>
      </message> </messages>
      
  syntax K ::= newAgent K
             | me
             | parent
             | receive
             | receiveFrom K     [strict]
             | send K to K       [strict]
             | sendSynch K to K  [strict]
             | barrier        
             | broadcast K       [strict]
             | haltAgent
             | #Int
             | #Bool

--- Agents
  rule [agent-creation] : <agent_> <k>newAgent S:K => N2:#Nat<_/k> <me>N1:#Nat</me> 
       <_/agent> <world_>. => SetItem(N2)<_/world> @latex("\\kBR")
       (. => <agent_><me>N2</me><parent>N1</parent><k>S</k><_/agent>) 
       <nextAgent>N2 => sNat N2</nextAgent> [large]
  rule [agent-completion] : (<agent_><control>.Bag</control> <me>N:#Nat</me> <_/agent>=> .) 
       <world_>(SetItem(N) => .)<_/world>
  rule [halt-agent] : <control_> <k>haltAgent<_/k> <_/control> => <control> .Bag </control> .
  rule <k>me => N<_/k> <me>N</me>
  rule <k>parent => N<_/k> <parent>N</parent>
  rule <me>N1</me> <k>send V to N2 => skip<_/k>
       (. => <message> <from>N1</from> <to>SetItem(N2)</to> <body>V</body> 
             </message>)
  rule <me>N</me> <k>receive=>V:KResult<_/k>
       <message_> <to_>SetItem(N)=>.<_/to> <body>V</body> <_/message>
  rule <message> <from>N2</from> <to_>SetItem(N1) => .<_/to> <body>V</body> 
       </message> <me>N1</me> <k>receiveFrom N2 => V<_/k>
  rule <me>N</me> <k>broadcast V => skip<_/k>
       <world>W:Set</world>
       (. => <message> <from>N</from> <to>W</to> <body>V</body> </message>)
  rule <message_><to>.Set</to><_/message> => . [structural]
  rule <agent_> <me>N1</me> <k>sendSynch V to N2 => skip<_/k> <_/agent> 
       <agent_><me>N2</me> <k>receiveFrom N1 => V<_/k> <_/agent>
  rule <k>sendSynch V to N2 => skip<_/k>
       <agent_><me>N2</me> <k>receive => V<_/k> <_/agent>
  rule [start-waiting-at-barrier] : <me>N</me> <k>barrier<_/k>
       <barrier>true</barrier> <waiting>W (. => SetItem(N))</waiting> 
    when notBool(SetItem(N) in W)
  rule [lifting-barrier] : <barrier>true=>false</barrier> <waiting>W</waiting> <world>W</world> 
    when W =/=Bool .
  rule [leave-barrier] : <me>N</me> <k>barrier => skip<_/k> <barrier>false</barrier>
       <waiting_>(SetItem(N) => .)<_/waiting>
  rule [lowering-barrier] : <barrier>false => true</barrier> <waiting>.Set</waiting>
end module
