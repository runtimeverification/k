

require /modules/exp
require /modules/if
require /modules/lambda
require /modules/mu
require /modules/callcc
require /modules/halt
require /modules/seq
require /modules/io
require /modules/ref
require /modules/while
require /modules/threads
require /modules/agents
require /modules/quote-unquote

module AGENT
  imports EXP 
  imports LAMBDA
  imports MU
  imports CALLCC
  imports HALT 
  imports IO 
  imports REF 
  imports WHILE 
  imports THREADS 
  imports AGENTS 
  imports QUOTE-UNQUOTE 

 configuration
    <T>
      <agent multiplicity="*"> 
          <control>
              <thread multiplicity="*">
                  <k color="green">$PGM:K</k>
                  <nextId>0</nextId>
                  <holds>.Map</holds>
              </thread>
          </control>
          <busy>.Set</busy> 
          @latex("\\kBR")
          <mem> .Map </mem> <nextLoc> 0 </nextLoc>
          <me>0</me>
          <parent>-1</parent>
      </agent>
      @latex("\\kBR")
      <nextAgent>1</nextAgent>
      <world>SetItem(0)</world>
      <barrier>true</barrier> <waiting>.Set</waiting>
      @latex("\\kBR")
      <messages> <message multiplicity="*">
          <from>.K</from> <to>.Set</to> <body>.K</body>
      </message> </messages>
      <I-O> <in stream="stdin">.List</in> <out stream="stdout">.List</out> </I-O>
    </T>

  syntax KResult ::= #Id
end module

