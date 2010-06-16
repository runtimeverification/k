
kmod IMPPP-SYNTAX is 
  including PL-INT + PL-ID
  op _+_ : AExp AExp -> AExp [gather(E e) prec 33 strict]
  op _/_ : AExp AExp -> AExp [gather(E e) prec 31 strict]
  op _<=_ : AExp AExp -> BExp [prec 37 metadata "latex(renameTo _\\ensuremath\\leq_)" seqstrict]
  op not_ : BExp -> BExp [prec 53 strict]
  op _and_ : BExp BExp -> BExp [gather(E e) prec 55 strict(1)]

  op var_; : Id -> Stmt [prec 2]
  op _=_; : Id AExp -> Stmt [prec 80 gather (e E) strict(2)]
  op ++_ : Id -> AExp [prec 0]

  op {} : -> Stmt [metadata "latex(renameTo \\{\\})"]
  op `{_`} : Stmt -> Stmt [gather(&) metadata "latex(renameTo \\{_\\})"]
  op __ : Stmt Stmt -> Stmt [prec 100 gather(e E)]
  op _; : AExp -> Stmt [prec 90 strict]
  op if_then_else_ : BExp Stmt Stmt -> Stmt [strict(1)]
  op while_do_ : BExp Stmt -> Stmt

  op read : -> AExp
  op print_; : AExp -> Stmt [strict]

  op spawn_ : Stmt -> Stmt [prec 90]

  op haltThread ; : -> Stmt

  sorts AExp BExp Stmt
  subsorts Int Id < AExp  subsort Bool < BExp 
endkm
