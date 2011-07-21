-------------------------
--- EXP-SYNTAX module ---
-------------------------

--- The modules below define the syntax of EXP.
--- We call the first one EXP-SYNTAX instead of EXP-UNTYPED-SYNTAX because we
--- want to use the same file exp-programs.k for both the untyped and the
--- type inferenced versions of the EXP languages.

kmod EXP-SYNTAX is including #INT + #ID
  syntax Exp ::= Int | Bool
               | Id
               | Exp + Exp                [strict prec 33 gather(E e)]
               | Exp - Exp                [strict prec 33 gather(E e)]
               | Exp * Exp                [strict prec 31 gather(E e)]
               | Exp / Exp                [strict prec 31 gather(E e)]
               | Exp % Exp                [strict prec 31 gather(E e)]
               | - Exp                    [strict]
               | Exp < Exp                [strict prec 37]
               | Exp <= Exp               [strict prec 37]
               | Exp > Exp                [strict prec 37]
               | Exp >= Exp               [strict prec 37]
               | Exp == Exp               [strict prec 37]
               | Exp != Exp               [strict prec 37]
               | Exp and Exp              [strict prec 55 gather(E e)]
               | Exp or Exp               [strict prec 59 gather(E e)]
               | not Exp                  [strict prec 53]
               | lambda Id . Exp          [latex "\lambda{#1}.{#2}"]
               | mu Id . Exp              [latex "\mu{#1}.{#2}"]
               | Exp Exp                  [strict prec 10 gather(E e)]
               | let Id = Exp in Exp
               | letrec Id Id = Exp in Exp
               | if Exp then Exp else Exp [strict(1)]
endkm


kmod EXP-UNTYPED-DESUGARED-SYNTAX is including EXP-SYNTAX
  macro let X:Id = E:Exp in E':Exp = (lambda X . E') E
  macro (letrec F:Id X = E in E') = (let F = mu F . (lambda X . E) in E')
endkm
