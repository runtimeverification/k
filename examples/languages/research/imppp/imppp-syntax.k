kmod IMPPP-SYNTAX is including #INT + #ID

  syntax AExp ::= Int | Id
                | AExp + AExp [gather(E e) prec 33 strict]
                | AExp / AExp [gather(E e) prec 31 strict]
                | ++ Id [prec 0]
                | read

  syntax BExp ::= Bool
                | AExp <= AExp [prec 37 latex "{#1}\leq{#2}" seqstrict]
                | not BExp [prec 53 strict]
                | BExp and BExp [gather(E e) prec 55 strict(1)]

  syntax Stmt ::= var Id ; [prec 2]
                | Id = AExp ; [prec 80 gather (e E) strict(2)]
                | { }
                | { Stmt } [gather(&)]
                | Stmt Stmt [prec 100 gather(e E)]
                | AExp ; [prec 90 strict]
                | if BExp then Stmt else Stmt [strict(1)]
                | while BExp do Stmt
                | spawn Stmt [prec 90]
                | haltThread ;
                | print AExp ; [strict]

endkm
