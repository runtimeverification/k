kmod DOT is including PL-INT + PL-NAT + PL-ID + PL-STRING + K
  syntax K ::= Graph( K , K , K , K )
	       | StrictKwd() 
	       | GraphKwd() | DigraphKwd()
	       | NodeStmt( K , K )
	       | EdgeStmt( K , K , K )
	       | IDStmt( K , K )
	       | AttrStmt( K , K )
	       | NodeID( K )
	       | EdgeRHS( K , K )
	       | EdgeOpDirected() | EdgeOpUndirected()
	       | Attr( K )
	       | AttrID( K )
	       | AttrIDAssign( K , K )
	       | GraphAttrKwd() | NodeAttrKwd() | EdgeAttrKwd()
	       | Subgraph( K , K )
	       | SubgraphKwd( K )
	       | None() | Some( K ) | Seq( K , K )
	       | Id | String | Int | Nat
endkm

  // macro [ (S:Nat ; Cg:Tree ; Cm:Tree ; Ng:Tree) ] = parse(S, Cg, Cm, Ng)
  // macro parse(0, .Tree, .Tree, .Tree) =
  //   <ps>
  //     <p><pColor>red</pColor><pCards>.Bag</pCards></p>
  //     <p><pColor>green</pColor><pCards>.Bag</pCards></p>
  //     <p><pColor>blue</pColor><pCards>.Bag</pCards></p>
  //     <p><pColor>purple</pColor><pCards>.Bag</pCards></p>
  //   </ps>
  // macro parse(S1:NzNat, Cg, Cm, Ng) =
  //   <s><sLoc>master</sLoc><sCards>.Bag</sCards></s>
  //   parse(absInt(S1 +Int -1), Cg, Cm, Ng)
  // macro parse(S, ((E1:Id -> E2:Id : C:Color T:Nat) , Cg), Cm, Ng) =
  //   <cEdge>
  //     <cFrom>E1</cFrom>
  //     <cTo>E2</cTo>
  //     <cColor>C</cColor>
  //     <cCost>T</cCost>
  //   </cEdge>
  //   parse(S, Cg, Cm, Ng)
  // rule (parse(S, Cg, (E1 -> E2 , Cm), Ng) => parse(S, Cg, Cm, Ng))
  //   <cCards_>. => (E1 |-> E2)<_/cCards> [structural]
  // macro parse(S, Cg, Cm, (E1 -> E2 : T , Ng)) =
  //   <nEdge>
  //     <nFrom>E1</nFrom>
  //     <nTo>E2</nTo>
  //     <nCost>T</nCost>
  //   </nEdge>
  //   parse(S, Cg, Cm, Ng)
