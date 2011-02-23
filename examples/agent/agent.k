load ../../k-prelude

load ../modules/exp
load ../modules/if
load ../modules/k-visitor
load ../modules/substitution
load ../modules/lambda
load ../modules/mu
load ../modules/callcc
load ../modules/halt
load ../modules/seq
load ../modules/io
load ../modules/ref
load ../modules/while
load ../modules/threads
load ../modules/agents
load ../modules/quote-unquote

load ../modules/tests/ids
load ../modules/tests/exp/programs
load ../modules/tests/lambda/programs
load ../modules/tests/mu/programs
load ../modules/tests/callcc/programs
load ../modules/tests/halt/programs
load ../modules/tests/io/programs
load ../modules/tests/imp/programs
load ../modules/tests/threads/programs
load ../modules/tests/agents/programs
load ../modules/tests/quote-unquote/programs

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
      <agent*> 
          <control>
              <thread*>
                  <k>.K</k>
                  <nextId>0</nextId>
                  <holds>.Map</holds>
              </thread*>
          </control>
          <busy>.Set</busy> 
          @latex("\\kBR")
          <mem> .Map </mem> <nextLoc> 0 </nextLoc>
          <me>0</me>
          <parent>-1</parent>
      </agent*>
      @latex("\\kBR")
      <nextAgent>1</nextAgent>
      <world>SetItem(0)</world>
      <barrier>true</barrier> <waiting>.Set</waiting>
      @latex("\\kBR")
      <messages> <message*>
          <from>.K</from> <to>.Set</to> <body>.K</body>
      </message*> </messages>
      <I/O> <in>.List</in> <out>.List</out> </I/O>
    </T>

  syntax KResult ::= Id

  syntax Bag ::= run ( KLabel ) | run ( KLabel , List{K} )

  macro run(KL:KLabel) = <T_> <k>KL(.List{K})</k> <_/T>
  macro run(KL:KLabel,L:List`{K`}) 
      = <T_> <k> KL(.List{K}) </k> <in>List(L)</in> <_/T>
endkm

