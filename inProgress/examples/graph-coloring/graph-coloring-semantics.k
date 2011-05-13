in graph-coloring-setup

kmod GRAPH-COLORING-SEMANTICS is including GRAPH-COLORING-SETUP
  kvar S N N1 N2 E1 E2 C P : K
  kvar L F TF T : Nat
  kvar Cs Ss Ps : Set

  // Tick
  rule <k> run </k>
    <all-edge-server-names> Ss </all-edge-server-names>
    <all-node-processor-names> Ps </all-node-processor-names>
    <working-server-names> . => Ss </working-server-names>
    <working-processor-names> . => Ps </working-processor-names>
    <time> T => sNat T </time>

  // Server advances
  rule <k> run </k>
    <server_>
      <s-name> S </s-name>
      <s-length> sNat L => L </s-length>
    <_/server>
    <working-server-names_> SetItem(S) => . <_/working-server-names>

  // Server arrives
  rule <k> run </k>
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
  rule <k> run </k>
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
  rule <k> run </k>
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
  rule <k> run </k>
    (<g-edge_>
      <ge-from> N1 </ge-from>
      <ge-to> N2 </ge-to>
      <ge-length> 0 </ge-length>
    <_/g-edge> => .)
    <g-edge_>
      <ge-from> N2 </ge-from>
      <ge-dependencies_> SetItem(N1) => . <_/ge-dependencies>
    <_/g-edge> [structural]

endkm
