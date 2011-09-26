require /modules/seq
require /modules/agents

require /modules/exp
require /modules/if
require /modules/lambda
require /modules/ref
require /modules/io
require /modules/while
require /modules/threads

require /modules/uris

module AGENTS-TEST is including AGENTS + THREADS + WHILE + IO + REF + LAMBDA + EXP + URIS
  configuration
    <T>
      <agent multiplicity="*"> 
          <control>
              <thread multiplicity="*">
                  <k>$PGM:K</k>
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
      <I-O> <in stream="stdin">.List</in> <out stream="stdout">.List</out> </I-O>
    </T>
end module
