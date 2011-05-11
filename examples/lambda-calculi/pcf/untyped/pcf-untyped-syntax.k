kmod PCF-UNTYPED-SYNTAX is including PL-ID + K-LATEX
  /*@ \section*{Syntax}
  This module defines the syntax for PCF.
  */

  syntax Val ::= Bool
               | Nat
               | succ
               | pred
               | zero?

  syntax Exp ::= Val
               | Id
               | Exp Exp            [strict prec 10 gather(E e)]
               | lambda Id . Exp    [latex "\lambda{#1}\mathbin{.}{#2}"]
               | mu Id . Exp        [latex "\mu{#1}\mathbin{.}{#2}"]
               | cond Exp Exp Exp   [strict(1)]

endkm
