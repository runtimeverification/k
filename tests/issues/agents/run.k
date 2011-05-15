in /modules/basic-run
in /modules/seq
in /modules/agents

load ../ids
in /modules/exp
in /modules/if
in /modules/k-visitor
in /modules/substitution
in /modules/lambda
in /modules/ref
in /modules/io
in /modules/while
in /modules/threads
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
