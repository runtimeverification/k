in ../../k/k-prelude
in graph-coloring-config

kmod GRAPH-COLORING-SETUP is including GRAPH-COLORING-CONFIG
  kvar S : K

  // [Randomly?] distribute cards
  rule <k> setup <_/k>
       <cards_> SetItem(S) => . <_/cards>
       <n-cards_> . => SetItem(S) <_/n-cards>

  // Clean up
  rule <k> setup => . <_/k>
       <cards> .Set </cards>

  // Start
  rule <k> start => . <_/k> <time> _ => 0 </time>

endkm