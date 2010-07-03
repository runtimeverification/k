kmod BOUNDING-EXP-SYNTAX is including PL-ID
  syntax Exp ::= Id
  syntax BoundingExp ::= Id -> Exp [prec 100 latex "{#1}.{#2}"]
endkm

kmod SUBSTITUTION is including BOUNDING-EXP-SYNTAX + PL-INT + K
---beta-substitution definition using the K AST visitor pattern
---assuming the binding operator is _->_
  syntax K ::= Exp | BoundingExp | Nat
             | K [ K / Id ] [prec 0]
             | beta List{K} [ K / Id ] 
               [prec 0 latex "{#1}\sqbracket{{#2}/_\beta{#3}}"]
             | beta-beta K [ K / Id ]  
               [prec 0 strict(1) latex "{#1}\sqbracket{{#2}/_\beta^0{#3}}"]
             | clearDone K [strict latex "{\it unbox}({#1})"]
  syntax KResult ::= done List{K}  [latex "\framebox{${#1}$}"]
  syntax Id ::= fresh Nat  --- to generate fresh names
  syntax CellLabel ::= nextId

  --- "boxed" versions of the K constructors (all of them are strict)
  syntax K ::= K box(~>) K [latex "{#1}\framebox{$\kra$}{#2}" strict]
             | K box(,,) K [latex "{#1}\framebox{$,\!\!,$}{#2}" strict]
  syntax KLabel ::= box ( KLabel ) [latex "\framebox{#1}"]
  context box(Label:KLabel)(_,,`[HOLE`]:K,,_)

  rule <k> K'[K:K/Y:Id] => clearDone(beta K'[K/Y]) <_/k> [structural]
  rule clearDone(done(K)) => K [structural] 

  rule beta Y[K/Y] => done(K) [structural]  ---this does the actual substitution
  rule <k> beta '_->_(X:Id,,K':K)[K/Y] => 
           box('_->_)(done(fresh(N)) box(,,) beta-beta beta K'[fresh(N)/X][K/Y])
      <_/k> <nextId>N:Nat => sNat N</nextId>
---    if Y =/=Bool X [structural] ---renaming bound variables
  rule beta-beta done(K')[K/Y] => beta K'[K/Y] [structural]
---  rule <k> beta '_->_(Y,,K':K)[K/Y] => done('_->_(Y,,K':K)) <_/k> [structural]
  rule beta .[K/Y] => done(.) [structural]
  rule beta((K1:K ~> K2:K))[K/Y] => beta K1[K/Y] box(~>) beta K2[K/Y]
    if K1 =/=Bool . andBool K2 =/=Bool . [structural]
  rule beta .List{K}[K/Y] => done(.List{K}) [structural]
  rule beta (K1,,K2,,Kl)[K/Y] 
    => beta K1[K/Y] box(,,) beta (K2,,Kl)[K/Y] [structural]
  rule beta Label(Kl)[K/Y] => box(Label)(beta Kl[K/Y])
    if Label =/=Bool '_->_ andBool Label(Kl) =/=Bool Y  [structural]

  rule box(Label)(done(Kl:List`{K`})) => done(Label(Kl)) [structural]
  rule done(Kl) box(,,) done(Kl':List`{K`}) => done((Kl,,Kl')) [structural]
  rule done(K1) box(~>) done(K2) => done((K1 ~> K2)) [structural]
endkm
