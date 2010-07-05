load ../../k-prelude

load ../modules/exp
load ../modules/k-visitor
load ../modules/substitution
load ../modules/lambda
load ../modules/mu
load ../modules/callcc
load ../modules/halt
load ../modules/io
load ../modules/ref
load ../modules/imp
load ../modules/threads
load ../modules/agents

kmod AGENT is 
  including EXP 
  including LAMBDA
  including MU
  including CALLCC
  including HALT 
  including IO 
  including REF 
  including IMP 
  including THREADS 
  including AGENTS 
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
          <mem> .Map </mem> <nextLoc> 0 </nextLoc>
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

