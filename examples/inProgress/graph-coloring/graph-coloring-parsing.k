in ../../k/k-prelude
in dot
in graph-coloring-programs
in graph-coloring-config

kmod GRAPH-COLORING-PARSING is including GRAPH-COLORING-CONFIG + GRAPH-COLORING-PROGRAMS + PL-CONVERSION
  // Running programs
  syntax Bag ::= [[ K ]] | e1 | e2 | e3 | e4 | e
  rule [[ P:K ]] => <top_> <k>P ~> servers(2) ~> setup ~> start ~> run</k> <_/top>
  macro e1 = [[ pcolors ]]
  macro e2 = [[ pcards ]]
  macro e3 = [[ pcg ]]
  macro e4 = [[ png ]]
  macro e = [[ full ]]

  // Parsing
  syntax CellLabel ::= name | from | to | color | length | cost | type
  kvar G S S1 S2 N1 N2 N : K
  kvar L C : String
  kvar M : Bag
  kvar Ds : Set
  kvar SS : Nat
  
  rule Seq(S1, S2) => S1 ~> S2 [structural]
  rule None() => . [structural]
  rule Some(S) => S [structural]
  rule Attr(S) => S [structural]
  rule NodeID(N) => N [structural]

  rule <k> Graph(_, _, "colors", S) => S <_/k> <graphType> _ => gtColors </graphType>
  rule <k> Graph(_, _, "cards",  S) => S <_/k> <graphType> _ => gtCards  </graphType>
  rule <k> Graph(_, _, "cg",     S) => S <_/k> <graphType> _ => gtcg     </graphType>
  rule <k> Graph(_, _, "ng",     S) => S <_/k> <graphType> _ => gtng     </graphType>

  rule <k> NodeStmt(S1, S)                 => S ~> NodeStmt(S1, .)     <_/k>  if S =/=Bool .K [structural]
  rule <k> EdgeStmt(N1, N2, S)             => S ~> EdgeStmt(N1, N2, .) <_/k>  if S =/=Bool .K [structural]

  rule <k> EdgeStmt(N1, N2, S)             => EdgeStmt(., N2, S)       <_/k> <meta_> . =>   < from > N1 </ from >   <_/meta>  if N1 =/=Bool .K
  rule <k> EdgeStmt(N1, EdgeRHS(_, N2), S) => EdgeStmt(N1, ., S)       <_/k> <meta_> . =>     < to > N2 </ to >     <_/meta>  if N2 =/=Bool .K
  rule <k> AttrIDAssign("name", S)         => .                        <_/k> <meta_> . =>   < name > S  </ name >   <_/meta>
  rule <k> AttrIDAssign("color", S)        => .                        <_/k> <meta_> . =>  < color > S  </ color >  <_/meta>
  rule <k> AttrIDAssign("length", S)       => .                        <_/k> <meta_> . => < length > S  </ length > <_/meta>
  rule <k> AttrIDAssign("cost", S)         => .                        <_/k> <meta_> . =>   < cost > S  </ cost >   <_/meta>
  rule <k> AttrIDAssign("type", S)         => .                        <_/k> <meta_> . =>   < type > S  </ type >   <_/meta>

  // List of colors; assign one processor per table that is not of "master" type
  rule <k> NodeStmt(S, .) => . <_/k> <graphType>gtColors</graphType>
       <meta>.Bag</meta>
       (. => <node_>
         <n-name> S </n-name>
         <processor>
           <p-name> S </p-name>
           <p-color> S </p-color>
         </processor>
       <_/node>)
  rule <k> NodeStmt(S, .) => . <_/k> <graphType>gtColors</graphType>
       <meta> (< type > "master" </ type > => .) </meta>
       <master>. => S</master>
       (. => <node_>
         <n-name> S </n-name>
       <_/node>)

  // Edge-to-card dependency graph
  rule <k> EdgeStmt(., ., .) => . <_/k> <graphType>gtCards</graphType>
       <meta>
        (< from > N1 </ from >
         < to > N2 </ to > => .)
       </meta>
       <ge-name> N1 </ge-name>
       <ge-cards_> . => SetItem(N2) <_/ge-cards>
       <cards_> . => SetItem(N2) <_/cards>

  // Edge from one node to another.  Calculate dependencies at the same time
  rule <k> EdgeStmt(., ., .) => . <_/k> <graphType>gtcg</graphType>
       <meta> 
        (< name > N </ name >
         < from > N1 </ from >
         < to > N2 </ to >
         < color > S </ color >
         < cost > C </ cost > => .)
       </meta>
       <dependencies_> . => SetItem(N) <_/dependencies>
       (. => <g-edge_>
         <ge-name> N </ge-name>
         <ge-from> N1 </ge-from>
         <ge-to> N2 </ge-to>
         <ge-color> S </ge-color>
         <ge-length> String2Int(C) </ge-length>
       <_/g-edge>)
  rule <dependencies_> SetItem(N) => . <_/dependencies>
       <g-edge_>
         <ge-name> N </ge-name>
         <ge-to> N2 </ge-to>
       <_/g-edge>
       <g-edge_>
         <ge-from> N2 </ge-from>
         <ge-dependencies_> . => SetItem(N) <_/ge-dependencies>
       <_/g-edge> [structural]

  // Network
  rule <k> EdgeStmt(., ., .) => . <_/k> <graphType>gtng</graphType>
       <meta>
        (< from > N1 </ from >
         < to > N2 </ to >
         < length > L </ length >
         < cost > C </ cost > => .)
       </meta>
       <n-name> N1 </n-name>
       (. => <n-edge_>
         <ne-to> N2 </ne-to>
         <ne-length> String2Int(L) </ne-length>
         <ne-cost> String2Int(C) </ne-cost>
         <ne-servers> .Bag </ne-servers>
       <_/n-edge>)

  // Generate servers at the master node
  rule <k> servers(sNat SS) => servers(SS) <_/k>
       <master> N </master>
       <n-name> N </n-name>
       <n-server-names_> . => SetItem(Int2String(SS)) <_/n-server-names>
  rule <k> servers(0) => . <_/k>

  // Cleanup
  rule <k> setup <_/k>
       <dependencies> Ds => .Set </dependencies>
       <graphType> G => .K </graphType>
       <meta> _ => .Bag </meta>
       if Ds =/=Bool .Set

endkm
