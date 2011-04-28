kmod GRAPH-COLORING-SEMANTICS is including GRAPH-COLORING-SETUP
  kvar S N N1 N2 E1 E2 C P : K
  kvar L F TF : Nat
  kvar Cs : Set

  // Server advances
  rule
    <server_>
      <s-name> S </s-name>
      <s-length> sNat L => L </s-length>
    <_/server>
    <working-server-names_> SetItem(S) => . <_/working-server-names>

  // Server arrives
  rule
    <ne-to> N </ne-to>
    <all-edge-server-names_> SetItem(S) => . <_/all-edge-server-names>
    (<server_>
      <s-name> S </s-name>
      <s-cards> Cs </s-cards>
      <s-length> 0 </s-length>
    <_/server> => .)
    <node_>
      <n-name> N </n-name>
      <n-cards_> . => Cs <_/n-cards>
      <n-server-names_> . => SetItem(S) <_/n-server-names>
    <_/node>  [structural]

  // Server leaves
  rule
    <all-edge-server-names_> . => SetItem(S) <_/all-edge-server-names>
    <ne-length> L </ne-length>
    <ne-cost> F </ne-cost>
    (. => <server_>
      <s-name> S </s-name>
      <s-cards> Cs </s-cards>
      <s-length> L </s-length>
    <_/server>)
    <node_>
      <n-cards_> Cs => . <_/n-cards>
      <n-server-names_> SetItem(S) => . <_/n-server-names>
    <_/node>
    <total-cost> TF => TF +Nat F </total-cost>

  // Processor colors
  rule
    <graph_>
      <ge-from> N1 </ge-from>
      <ge-to> N2 </ge-to>
      <ge-color> C </ge-color>
      <ge-length> sNat L => L </ge-length>
      <ge-cards> Cs </ge-cards>
      <ge-dependencies> .Set </ge-dependencies>
    <_/graph>
    <processor_>
      <p-name> P </p-name>
      <p-color> C </p-color>
    <_/processor>
    <working-processor-names_> SetItem(P) => . <_/working-processor-names>

  // Graph dependencies update
  rule
    <g-edge_>
      <ge-from> N1 </ge-from>
      <ge-to> N2 </ge-to>
      <ge-length> 0 </ge-length>
    <_/g-edge>
    <g-edge_>
      <ge-from> N2 </ge-from>
      <ge-dependencies_> SetItem(N1) => . <_/ge-dependencies>
    <_/g-edge> [structural]

endkm
