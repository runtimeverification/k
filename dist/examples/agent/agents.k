require "seq.k"

module AGENTS-SYNTAX imports SEQ-SYNTAX
  syntax K ::= Int | Bool
             | "newAgent" K
             | "me"
             | "parent"
             | "receive"
             | "receiveFrom" K     [strict]
             | "send" K "to" K       [strict]
             | "sendSynch" K "to" K  [strict]
             | "barrier"        
             | "broadcast" K       [strict]
             | "haltAgent"
endmodule

module AGENTS 
  imports AGENTS-SYNTAX
  imports SEQ
  configuration
      <agent multiplicity="*"> 
          <me>0</me>
          <parent>-1</parent>
          <control> <k color="green"> .K </k> </control>
      </agent> 
//      <br/>
      <nextAgent>1</nextAgent>
      <world>SetItem(0)</world>
      <barrier>true</barrier> <waiting>.Set</waiting> 
//      <br/>
      <messages> <message multiplicity="*">
          <from>.K</from> <to>.Set</to> <body>.K</body>
      </message> </messages>
      

// Agents
  rule [agent-creation] : <agent>...  <k>newAgent S:K => N2:Nat ...</k> <me>N1:Nat</me> 
        ...</agent> <world>... . => SetItem(N2) ...</world> // <br/>
       (. => <agent>... <me>N2</me><parent>N1</parent><k>S</k> ...</agent>) 
       <nextAgent>N2 => N2 +Int 1</nextAgent>
  rule [agent-completion] : (<agent>... <control>.Bag</control> <me>N:Nat</me>  ...</agent>=> .) 
       <world>... (SetItem(N) => .) ...</world>
  rule [halt-agent] : <control>...  <k>haltAgent ...</k>  ...</control> => <control> .Bag </control> .
  rule <k>me => N ...</k> <me>N</me>
  rule <k>parent => N ...</k> <parent>N</parent>
  rule <me>N1</me> <k>send V to N2 => skip ...</k>
       (. => <message> <from>N1</from> <to>SetItem(N2)</to> <body>V</body> 
             </message>)
  rule <me>N</me> <k>receive=>V:KResult ...</k>
       <message>...  <to>... SetItem(N)=>. ...</to> <body>V</body>  ...</message>
  rule <message> <from>N2</from> <to>... SetItem(N1) => . ...</to> <body>V</body> 
       </message> <me>N1</me> <k>receiveFrom N2 => V ...</k>
  rule <me>N</me> <k>broadcast V => skip ...</k>
       <world>W:Set</world>
       (. => <message> <from>N</from> <to>W</to> <body>V</body> </message>)
  rule <message>... <to>.Set</to> ...</message> => . [structural]
  rule <agent>...  <me>N1</me> <k>sendSynch V to N2 => skip ...</k>  ...</agent> 
       <agent>... <me>N2</me> <k>receiveFrom N1 => V ...</k>  ...</agent>
  rule <k>sendSynch V to N2 => skip ...</k>
       <agent>... <me>N2</me> <k>receive => V ...</k>  ...</agent>
  rule [start-waiting-at-barrier] : <me>N</me> <k>barrier ...</k>
       <barrier>true</barrier> <waiting>W (. => SetItem(N))</waiting> 
    when notBool(SetItem(N) in W)
  rule [lifting-barrier] : <barrier>true=>false</barrier> <waiting>W</waiting> <world>W</world> 
    when W =/=Set .
  rule [leave-barrier] : <me>N</me> <k>barrier => skip ...</k> <barrier>false</barrier>
       <waiting>... (SetItem(N) => .) ...</waiting>
  rule [lowering-barrier] : <barrier>false => true</barrier> <waiting>.Set</waiting>
endmodule
