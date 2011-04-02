kmod BINARY-TREE-HP is
  including MATCHC-SEMANTICS
          + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE
          + MATHEMATICAL-TREE-BUILTIN-MODULE

  kvar N : Nat
  kvar P P' Q Q1 Q2 : Int++
  kvar I : Int++
  kvar Alpha : Seq++
  kvar Sigma Tau : Tree++
  kvar H : Map
  kvar K : K
  kvar Phi : Formula
  kvar CfgItems TaskItems : Bag


*** Definition of Trees ***
  rule
  (
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> tree(P)(Tau) H </heap>
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi </form>
      TaskItems
    </task>
  =>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> H </heap>
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi /\ (P === 0) /\ (Tau === upsilon) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> K </k>
        <heap>
          P |-> FreeInt(N) : (id("treeNode").id("val"))
          (P +Int 1) |-> FreeInt(N +Int 1) : (id("treeNode").id("left"))
          (P +Int 2) |-> FreeInt(N +Int 2) : (id("treeNode").id("right"))
          tree(FreeInt(N +Int 1))(FreeTree(N +Int 3))
          tree(FreeInt(N +Int 2))(FreeTree(N +Int 4))
          H
        </heap>
        <counter> N +Int 5 </counter>
        CfgItems
      </config>
      <form>
        Phi /\ ~(P === 0)
        /\ (Tau === (FreeTree(N +Int 3) [FreeInt(N)] FreeTree(N +Int 4)))
      </form>
      TaskItems
    </task>
  )
  if VALID(Phi ===> P' === P \/ P' === P +Int 1 \/ P' === P +Int 2)
  [structural]

  rule
    <heap_> tree(0)(Tau) => .Map <_/heap>
    <form> Phi => Phi /\ Tau === upsilon </form>
  [structural]
  rule
    <heap_> tree(P)(upsilon) => .Map <_/heap>
    <form> Phi => Phi /\ P === 0 <_/form>
  [structural]

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("treeNode").id("val"))
        (P +Int 1) |-> 0 : (id("treeNode").id("left"))
        (P +Int 2) |-> 0 : (id("treeNode").id("right"))
      =>
        tree(P)(upsilon [I] upsilon)
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("treeNode").id("val"))
        (P +Int 1) |-> Q : (id("treeNode").id("left"))
        (P +Int 2) |-> 0 : (id("treeNode").id("right"))
        tree(Q)(Tau)
      =>
        tree(P)(Tau [ I ] upsilon)
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("treeNode").id("val"))
        (P +Int 1) |-> 0 : (id("treeNode").id("left"))
        (P +Int 2) |-> Q : (id("treeNode").id("right"))
        tree(Q)(Tau)
      =>
        tree(P)(upsilon [ I ] Tau)
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("treeNode").id("val"))
        (P +Int 1) |-> Q1 : (id("treeNode").id("left"))
        (P +Int 2) |-> Q2 : (id("treeNode").id("right"))
        tree(Q1)(Tau)
        tree(Q2)(Sigma)
      =>
        tree(P)(Tau [ I ] Sigma)
    <_/heap>


*** Definition of Lists of Trees ***
  rule 
  (
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> treeList(P)(Alpha) H </heap>
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi </form>
      TaskItems
    </task>
  =>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> H </heap>
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi /\ (P === 0) /\ (Alpha === epsilon) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> K </k>
        <heap>
          P |-> FreeInt(N) : (id("stackNode").id("val"))
          (P +Int 1) |-> FreeInt(N +Int 1) : (id("stackNode").id("next"))
          tree(FreeInt(N))(FreeTree(N +Int 2))
          treeList(FreeInt(N +Int 1))(FreeSeq(N +Int 3))
          H
        </heap>
        <counter> N +Int 4 </counter>
        CfgItems
      </config>
      <form>
        Phi /\ ~(P === 0) /\ ~(FreeInt(N) === 0)
        /\ (Alpha === [FreeTree(N +Int 2)] @ FreeSeq(N +Int 3))
      </form>
      TaskItems
    </task>
  )
  if VALID(Phi ===> P' === P \/ P' === P +Int 1)
  [structural]

  rule
    <heap_> treeList(0)(Alpha) => .Map <_/heap>
    <form> Phi => Phi /\ Alpha === epsilon </form>
  [structural]

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("stackNode").id("val"))
        (P +Int 1) |-> 0 : (id("stackNode").id("next"))
        tree(I)(Tau)
      =>
        treeList(P)([Tau])
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("stackNode").id("val"))
        (P +Int 1) |-> Q : (id("stackNode").id("next"))
        tree(I)(Tau)
        treeList(Q)(Alpha)
      =>
        treeList(P)([Tau] @ Alpha)
    <_/heap>
endkm 
