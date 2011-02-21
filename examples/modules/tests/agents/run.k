load ../basic-run
load ../../seq
load ../../agents

load ../ids
load ../../exp
load ../../if
load ../../k-visitor
load ../../substitution
load ../../lambda
load ../../ref
load ../../io
load ../../while
load ../../threads
load programs

kmod RUN is including AGENTS-PROGRAMS + BASIC-RUN
  configuration
    <T>
      <agent multiplicity="*"> 
          <control>
              <thread multiplicity="*">
                  <k>.K</k>
                  <nextId>0</nextId>
                  <holds>.Map</holds>
                  <mem>.Map</mem> <nextLoc>0</nextLoc>
              </thread>
          </control>
          <busy>.Set</busy>
          <me>0</me>
          <parent>-1</parent>
      </agent>
      <nextAgent>1</nextAgent>
      <world>SetItem(0)</world>
      <barrier>true</barrier> <waiting>.Set</waiting>
      <messages> <message multiplicity="*">
          <from>.K</from> <to>.Set</to> <body>.K</body>
      </message> </messages>
      <I-O> <in>.List</in> <out>.List</out> </I-O>
    </T>
endkm
