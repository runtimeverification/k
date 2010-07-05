load basic-run
load exp
load ../substitution/substitution
load fun
load control
load io
load ref
load imp
load threads
load agents

kmod MODULAR-AGENT is 
  including EXP 
  including FUN 
  including CONTROL 
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

