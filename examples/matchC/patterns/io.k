kmod IO-PATTERN is
  including MATCHC-SEMANTICS + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE

  kvar N : Nat
  kvar I : Int++
  kvar Alpha Beta : Seq++
  kvar NeAlpha NeBeta : NeSeq++
  kvar T : ExpressionType
  kvar K : K
  kvar List : List
  kvar NeList : NeList
  kvar Phi : Formula
  kvar CfgItems TaskItems : Bag


  rule
    <task>
      <taskType> Run </taskType>
      <config>
        <k> read(T) ~> K </k>
        <in> stream(NeAlpha) List </in>
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
        <k> read(T) ~> K </k>
        <in> List </in>
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi /\ (NeAlpha === epsilon) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config >
        <k> read(T) ~> K </k>
        <in> ListItem(FreeInt(N)) stream(FreeSeq(N +Int 1)) List </in>
        <counter> N +Int 2 </counter>
        CfgItems
      </config>
      <form>
        Phi /\ (NeAlpha === [FreeInt(N)] @ FreeSeq(N +Int 1))
      </form>
      TaskItems
    </task>
  [structural]

  rule
    <taskType> Run </taskType>
    <in> .List => stream(epsilon) </in>
  [structural]
  rule
    <taskType> Run </taskType>
    <in> (stream(epsilon) => .List) NeList </in>
  [structural]
  rule
    <taskType> Run </taskType>
    <in_> stream([I]) => ListItem(I) <_/in>
  [structural]
  rule 
    <taskType> Run </taskType>
    <in_> stream(NeAlpha @ NeBeta) => stream(NeAlpha) stream(NeBeta) <_/in>
  [structural]

  rule
    <taskType> Hypothesis </taskType>
    <in_> ListItem(I) => stream([I]) <_/in>
  [structural]
  rule 
    <taskType> Hypothesis </taskType>
    <in_> stream(Alpha) stream(Beta) => stream(Alpha @ Beta) <_/in>
  [structural]


  rule
    <taskType> Run </taskType>
    <out> .List => stream(epsilon) </out>
  [structural]
  rule <out_> ListItem(I) => stream([I]) <_/out> [structural]
  rule
    <out_> stream(Alpha) stream(Beta) => stream(Alpha @ Beta) <_/out>
  [structural]
endkm

