kmod REFLECTION is including K
  syntax KResult ::= done List{K}  [latex "\framebox{${#1}$}"]
  --- "boxed" versions of the K constructors (all of them are strict)
  syntax K ::= K box(~>) K [latex "{#1}\framebox{$\kra$}{#2}" strict]
             | K box(,,) K [latex "{#1}\framebox{$,\!\!,$}{#2}" strict]
  syntax KLabel ::= box ( KLabel ) [latex "\framebox{#1}"]
  context box(Label:KLabel)(_,,`[HOLE`]:K,,_)

  syntax K ::= clearDone K [strict latex "{\it unbox}({#1})"]
  rule clearDone(done(K:K)) => K [structural] 

  rule box(Label)(done(Kl:List`{K`})) => done(Label(Kl)) [structural]
  rule done(Kl) box(,,) done(Kl':List`{K`}) => done((Kl,,Kl')) [structural]
  rule done(K1:K) box(~>) done(K2:K) => done((K1 ~> K2)) [structural]
endkm

kmod SUBSTITUTION is including PL-ID + PL-INT + REFLECTION
---beta-substitution definition using the K AST visitor pattern
---assuming the binding operator is [_]_
  syntax K ::= Id | [ Id ] K | Nat
             | K [ K / Id ] [prec 0]
             | beta List{K} [ K / Id ] 
               [prec 0 latex "{#1}\sqbracket{{#2}/_\beta{#3}}"]
             | beta-beta K [ K / Id ]  
               [prec 0 strict(1) latex "{#1}\sqbracket{{#2}/_\beta^0{#3}}"]
  syntax Id ::= fresh Nat  --- to generate fresh names
  configuration <k> .K </k> <nextId> 0 </nextId>

  rule <k> K'[K:K/Y:Id] => clearDone(beta K'[K/Y]) <_/k> [structural]

  rule beta Y[K/Y] => done(K) [structural]  ---this does the actual substitution
  rule <k> beta '`[_`]_(X:Id,,K':K)[K/Y] => 
           box('`[_`]_)(done(fresh(N)) box(,,) beta-beta beta K'[fresh(N)/X][K/Y])
      <_/k> <nextId>N:Nat => sNat N</nextId>
---    if Y =/=Bool X [structural] ---renaming bound variables
  rule beta-beta done(K')[K/Y] => beta K'[K/Y] [structural]
---  rule <k> beta '`[_`]_(Y,,K':K)[K/Y] => done('`[_`]_(Y,,K':K)) <_/k> [structural]
  rule beta .[K/Y] => done(.) [structural]
  rule beta((K1:K ~> K2:K))[K/Y] => beta K1[K/Y] box(~>) beta K2[K/Y]
    if K1 =/=Bool . andBool K2 =/=Bool . [structural]
  rule beta .List{K}[K/Y] => done(.List{K}) [structural]
  rule beta (K1,,NeKl:NeList`{K`})[K/Y] 
    => beta K1[K/Y] box(,,) beta (NeKl)[K/Y] [structural]
  rule beta Label(Kl:List`{K`})[K/Y] => box(Label)(beta Kl[K/Y])
    if Label:KLabel =/=Bool '`[_`]_ andBool Label(Kl) =/=Bool Y  [structural]
endkm
