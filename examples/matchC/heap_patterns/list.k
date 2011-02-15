kmod LIST-HP is
  including MATCHC-SEMANTICS + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE

  kvar N : Nat
  kvar P P' Q Q1 Q2 : Int++
  kvar I : Int++
  kvar Alpha Beta : Seq++
  kvar H : Map
  kvar K : K
  kvar Phi : Formula
  kvar CfgItems TaskItems : Bag


*** Definition of Lists ***
  rule
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> list(P)(Alpha) H </heap>
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
      <config >
        <k> K </k>
        <heap>
          P |-> FreeInt(N) : (id("listNode").id("val"))
          (P +Int 1) |-> FreeInt(N +Int 1) : (id("listNode").id("next"))
          list(FreeInt(N +Int 1))(FreeSeq(N +Int 2))
          H
        </heap>
        <counter> N +Int 3 </counter>
        CfgItems
      </config>
      <form>
        Phi /\ ~(P === 0) /\ (Alpha === [FreeInt(N)] @ FreeSeq(N +Int 2))
      </form>
      TaskItems
    </task>
  if VALID(Phi ===> P' === P \/ P' === P +Int 1)
  [structural]

  rule
    <taskType> Run </taskType>
    <heap>
        list(P)(Alpha)
      =>
        P |-> FreeInt(N) : (id("listNode").id("val"))
        (P +Int 1) |-> FreeInt(N +Int 1) : (id("listNode").id("next"))
        list(FreeInt(N +Int 1))(FreeSeq(N +Int 2))
    <_/heap>
    <counter> N => N +Int 3 </counter>
    <form>
      Phi /\ ~(P === 0) => Phi /\ ~(P === 0) /\ (Alpha === [FreeInt(N)] @ FreeSeq(N +Int 2))
    </form>
  [structural]

  rule
    <heap_> list(0)(Alpha) => .Map <_/heap>
    <form> Phi => Phi /\ Alpha === epsilon </form>
  [structural]
  rule
    <heap_> list(P)(epsilon) => .Map <_/heap>
    <form> Phi => Phi /\ P === 0 </form>
  [structural]

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("listNode").id("val"))
        (P +Int 1) |-> 0 : (id("listNode").id("next"))
      => 
        list(P)([I])
    <_/heap>
  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("listNode").id("val"))
        (P +Int 1) |-> P' : (id("listNode").id("next"))
        list(P')(Alpha)
      =>     
        list(P)([I] @ Alpha)
    <_/heap>


*** Definition of List Segments ***
  rule
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> lseg(P, Q)(Alpha) H </heap>
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi </form>
      TaskItems
    </tasks>
  =>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> H </heap> 
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi /\ (P === Q) /\ (Alpha === epsilon) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config >
        <k> K </k>
        <heap>
          P |-> FreeInt(N) : (id("listNode").id("val"))
          (P +Int 1) |-> FreeInt(N +Int 1) : (id("listNode").id("next"))
          lseg(FreeInt(N +Int 1), Q)(FreeSeq(N +Int 2))
          H
        </heap>
        <counter> N +Int 3 </counter>
        CfgItems
      </config>
      <form>
        Phi /\ ~(P === Q) /\ (Alpha === [FreeInt(N)] @ FreeSeq(N +Int 2))
      </form>
      TaskItems
    </task>
  if VALID(Phi ===> P' === P \/ P' === P +Int 1)
  [structural]

  rule
    <heap_> lseg(P, P)(Alpha) => .Map <_/heap>
    <form> Phi => Phi /\ Alpha === epsilon </form>
  [structural]
  rule
    <heap> lseg(P, 0)(Alpha) => list(P)(Alpha) <_/heap>
  [structural]

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("listNode").id("val"))
        (P +Int 1) |-> Q : (id("listNode").id("next"))
      =>
        lseg(P, Q)([I])
    <_/heap>
     
  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        lseg(P, P')(Alpha)
        lseg(P', Q)(Beta)
      =>
        lseg(P, Q)(Alpha @ Beta)
    <_/heap>
     
  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        lseg(P, P')(Alpha)
        list(P')(Beta)
      =>
        list(P)(Alpha @ Beta)
    <_/heap>
endkm
