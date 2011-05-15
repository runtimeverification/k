

in /modules/exp
in /modules/if
in /modules/k-visitor
in /modules/substitution
in /modules/lambda
in /modules/mu
in /modules/callcc
in /modules/halt
in /modules/seq
in /modules/io
in /modules/ref
in /modules/while
in /modules/threads
in /modules/agents
in /modules/quote-unquote

load ../../../../tests/regression/ids
load ../../../../tests/regression/exp/programs
load ../../../../tests/regression/lambda/programs
load ../../../../tests/regression/mu/programs
load ../../../../tests/regression/callcc/programs
load ../../../../tests/regression/halt/programs
load ../../../../tests/regression/io/programs
load ../../../../tests/regression/imp/programs
load ../../../../tests/regression/threads/programs
load ../../../../tests/regression/agents/programs
load ../../../../tests/regression/quote-unquote/programs

kmod AGENT is 
  including EXP 
  including LAMBDA
  including MU
  including CALLCC
  including HALT 
  including IO 
  including REF 
  including WHILE 
  including THREADS 
  including AGENTS 
  including QUOTE-UNQUOTE 

   including EXP-PROGRAMS + LAMBDA-PROGRAMS + MU-PROGRAMS + CALLCC-PROGRAMS
   including HALT-PROGRAMS + IO-PROGRAMS + IMP-PROGRAMS 
   including THREADS-PROGRAMS + AGENTS-PROGRAMS + QUOTE-UNQUOTE-PROGRAMS
 configuration
    <T>
      <agent multiplicity="*"> 
          <control>
              <thread multiplicity="*">
                  <k>.K</k>
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
      <I-O> <in>.List</in> <out>.List</out> </I-O>
    </T>

  syntax KResult ::= Id

  syntax Bag ::= run ( KLabel ) | run ( KLabel , List{K} )

  macro run(KL:KLabel) = <T_> <k>KL(.List{K})</k> <_/T>
  macro run(KL:KLabel,L:List`{K`}) 
      = <T_> <k> KL(.List{K}) </k> <in>List(L)</in> <_/T>
endkm

