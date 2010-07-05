load ../basic-run
load ../../agents

load ../ids
load ../../exp
load ../../k-visitor
load ../../substitution
load ../../fun
load ../../io
load ../../imp
load ../../threads
load programs

kmod RUN is including AGENTS-PROGRAMS + BASIC-RUN
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
