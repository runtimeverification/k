kmod EXP-TYPE-INFERENCE-SEMANTICS is including EXP-TYPE-INFERENCE-DESUGARED-SYNTAX + UNIFICATION 
  syntax Exp ::= Type
  syntax K ::= Exp | List{TypeSchema}
  syntax KResult ::= Type

  configuration <T>
                     <k> .K </k>
                     <tenv> .Map </tenv>
                     <eqns> <eqn multiplicity="*"> .Set </eqn>
                            <started> .Set </started>
                            <solved> .Set </solved>
                     </eqns>
                     <nextType> tvar(0) </nextType>
                </T>

  rule <k> (I:#Int => int) <_/k>
  rule <k> (B:#Bool => bool) <_/k>
  rule <k> (X:#Id => T:Type) <_/k> <tenv_> X|->T <_/tenv>
  rule <k> (L:KLabel(T1:Type,,T2:Type) => int) <_/k> (.Bag => <eqn> T1 = int </eqn> <eqn> T2 = int </eqn>)
    if L ==Bool '_+_ orBool L ==Bool '_-_ orBool L ==Bool '_*_ orBool L ==Bool '_/_ orBool L ==Bool '_%_
  rule <k> (- T => int) <_/k> (.Bag => <eqn> T = int </eqn>)
  rule <k> (L(T1,,T2) => bool) <_/k> (.Bag => <eqn> T1 = int </eqn> <eqn> T2 = int </eqn>)
    if L ==Bool '_<_ orBool L ==Bool '_<=_ orBool L ==Bool '_>_ orBool L ==Bool '_>=_ orBool L ==Bool '_==_ orBool L ==Bool '_!=_
  rule <k> (L(T1,,T2) => bool) <_/k> (.Bag => <eqn> T1 = bool </eqn> <eqn> T2 = bool </eqn>)
    if L ==Bool '_and_ orBool L ==Bool '_or_
  rule <k> (not T => bool) <_/k> (.Bag => <eqn> T = bool </eqn>)
  rule <k> (if T then T1 else T2 => T1) <_/k> (.Bag => <eqn> T = bool </eqn> <eqn> T1 = T2 </eqn>)

  rule <k> lambda X . E:Exp => E ~> mkFunType(Tv:#TypeVar) ~> tenv(TEnv:Map) <_/k>
          <tenv> TEnv => TEnv[Tv/X] </tenv> <nextType> (Tv => Tv +Type 1) </nextType>
  rule <k> T1 T2 => Tv <_/k> (.Bag => <eqn> T1 = (T2 -> Tv) </eqn>) <nextType> Tv => Tv +Type 1 </nextType>

  rule <k> mu X . E => E ~> addEqn(Tv) ~> tenv(TEnv) <_/k>
          <tenv> TEnv => TEnv[Tv / X] </tenv> <nextType> (Tv => Tv +Type 1) </nextType>

  rule <k> let X = T in E => E ~> tenv(TEnv) <_/k> <eqns> <started> .Set </started> <solved> Eqns:Set </solved> </eqns>
          <tenv> TEnv => TEnv[forall (ftv(Eqns[T]) \ ftv(Eqns[[types(TEnv)]])) . Eqns[T] / X] </tenv>
  rule <k> X => T[| Tvl:List{TypeVar} | from Tv / Tvl] <_/k> <tenv_> X |-> forall Tvl . T <_/tenv>
          <nextType> Tv => Tv +Type | Tvl | </nextType>


------------------------
--- Auxilliary stuff ---
------------------------

  syntax K ::= mkFunType #TypeVar [latex "({#1}\rightarrow\square)"] | addEqn Type | tenv Map
  rule T ~> mkFunType(Tv) => Tv -> T
  rule <k> T ~> addEqn(Tv) => Tv <_/k> (.Bag => <eqn> Tv = T </eqn>)
  rule <k> T ~> (tenv(TEnv) => .K) <_/k> <tenv>  _  => TEnv </tenv> [structural]

--- next should probably be generic in some way, for all maps ..
  op types_ : Map -> List{Type} 
  eq types(.Map) = .List{TypeVar} 
  eq types(X |-> T TEnv) = T,types(TEnv) 
endkm
