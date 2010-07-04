load ../basic-run
load ../exp
load ../imp
load ../agents

load ../ids
load ../../substitution/substitution
load ../fun
load ../io
load ../threads
load agents-programs

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