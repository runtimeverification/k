// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "int.k"
require "bool.k"
require "seq.k"

module AGENTS-SYNTAX imports SEQ-SYNTAX
  imports INT-EXP-SYNTAX
  imports BOOL-EXP-SYNTAX
  syntax Exp ::= "newAgent" Exp [newAg]
             | "me" [me]
             | "parent" [parent]
             | "receive" [rcv]
             | "receiveFrom" Exp     [rcvFr, strict]
             | "send" Exp "to" Exp       [sndTo, strict]
             | "sendSynch" Exp "to" Exp  [sndSyn, strict]
             | "barrier"        [bar]
             | "broadcast" Exp       [bcst, strict]
             | "haltAgent" [haltAg]
endmodule

module AGENTS
  imports AGENTS-SYNTAX
  imports SEQ
  imports INT-EXP
  imports BOOL-EXP
  configuration
      <agent multiplicity="*">
          <me>0</me>
          <parent>-1</parent>
          <control> <k color="green"> .K </k> </control>
      </agent>
//      <br/>
      <world>SetItem(0)</world>
      <barrier>true</barrier> <waiting>.Set</waiting>
//      <br/>
      <messages> <message multiplicity="*">
          <from>.K</from> <to>.Set</to> <body>.K</body>
      </message> </messages>


// Agents
  rule [agent-creation] : <agent>...  <k>newAgent S:K => !N2:Int ...</k> <me>N1:Int</me>
        ...</agent> <world>... .Set => SetItem(!N2) ...</world> // <br/>
       (. => <agent>... <me>!N2</me><parent>N1</parent><k>S</k> ...</agent>)
  rule [agent-completion] : (<agent>... <control>.Bag</control> <me>N:Int</me>  ...</agent>=> .)
       <world>... (SetItem(N) => .Set) ...</world>
  rule [halt-agent] : <control>...  <k>haltAgent ...</k>  ...</control> => <control> .Bag </control>
    [transition]
  rule <k>me => N ...</k> <me>N</me>
  rule <k>parent => N ...</k> <parent>N</parent>
  rule <me>N1</me> <k>send V:Val to N2 => skip ...</k>
       (. => <message> <from>N1</from> <to>SetItem(N2)</to> <body>V</body>
             </message>)
  rule <me>N</me> <k>receive=>V:Val ...</k>
       <message>...  <to>... SetItem(N) => .Set ...</to> <body>V</body>  ...</message>
    [transition]
  rule <message> <from>N2</from> <to>... SetItem(N1) => .Set ...</to> <body>V</body>
       </message> <me>N1</me> <k>receiveFrom N2 => V ...</k>
    [transition]
  rule <me>N</me> <k>broadcast V => skip ...</k>
       <world>W:Set</world>
       (. => <message> <from>N</from> <to>W</to> <body>V</body> </message>)
  rule <message>... <to>.Set</to> ...</message> => . [structural]
  rule <agent>...  <me>N1</me> <k>sendSynch V to N2 => skip ...</k>  ...</agent>
       <agent>... <me>N2</me> <k>receiveFrom N1 => V ...</k>  ...</agent>
    [transition]
  rule <k>sendSynch V to N2 => skip ...</k>
       <agent>... <me>N2</me> <k>receive => V ...</k>  ...</agent>
    [transition]
  rule [start-waiting-at-barrier] : <me>N</me> <k>barrier ...</k>
       <barrier>true</barrier> <waiting>W (.Set => SetItem(N))</waiting>
    when notBool(N in W)
  rule [lifting-barrier] : <barrier>true=>false</barrier> <waiting>W</waiting> <world>W</world>
    when W =/=K .Set
    [transition]
  rule [leave-barrier] : <me>N</me> <k>barrier => skip ...</k> <barrier>false</barrier>
       <waiting>... (SetItem(N) => .Set) ...</waiting>
  rule [lowering-barrier] : <barrier>false => true</barrier> <waiting>.Set</waiting>
endmodule
