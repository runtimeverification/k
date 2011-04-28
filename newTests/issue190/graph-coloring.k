in ../../k/k-prelude
in dot
in graph-coloring-programs
in graph-coloring-parsing
in graph-coloring-setup
in graph-coloring-semantics

kmod GRAPH-COLORING is including GRAPH-COLORING-SEMANTICS
  syntax Bag ::= [[ K ]] | e1 | e2 | e3 | e4 | e
  rule [[ P:K ]] => <top_> <k>P ~> servers(2) ~> setup ~> start ~> run</k> <_/top>
  macro e1 = [[ pcolors ]]
  macro e2 = [[ pcards ]]
  macro e3 = [[ pcg ]]
  macro e4 = [[ png ]]
  macro e = [[ full ]]
  
endkm