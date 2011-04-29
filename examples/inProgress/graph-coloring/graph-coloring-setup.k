kmod GRAPH-COLORING-SETUP is including GRAPH-COLORING-PARSING
  kvar SS : Nat
  kvar N S G : K
  kvar Ds : Set

  // Generate servers at the master node
  rule <k> servers(sNat SS) => servers(SS) <_/k>
       <master> N </master>
       <n-name> N </n-name>
       <n-server-names_> . => SetItem(Int2String(SS)) <_/n-server-names>
  rule <k> servers(0) => . <_/k>

  // [Randomly?] distribute cards
  rule <k> setup <_/k>
       <cards_> SetItem(S) => . <_/cards>
       <n-cards_> . => SetItem(S) <_/n-cards>

  // Clean up
  rule <k> setup => . <_/k>
       <cards> .Set </cards>
       <dependencies> Ds => .Set </dependencies>
       <graphType> G => .K </graphType>
       <meta> _ => .Bag </meta>
       if Ds =/=Bool .Set

  // Start
  rule <k> start => . <_/k> <time> _ => 0 </time>

endkm