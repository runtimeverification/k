kmod PCF-UNTYPED-SYNTAX is including #ID + K-LATEX
  /*@ \section*{Syntax}
  This module defines the syntax for PCF.
  */

  syntax Val ::= #Bool
               | #Nat
               | succ
               | pred
               | zero?

  /*@ Removing the strictness attribute on the production for application gives
  us a call-by-name variant of PCF.
  */
  syntax Exp ::= Val
               | #Id
               | Exp Exp            [strict prec 10 gather(E e)]
               | lambda #Id . Exp    [latex "\lambda{#1}\mathbin{.}{#2}"]
               | mu #Id . Exp        [latex "\mu{#1}\mathbin{.}{#2}"]
               | cond Exp Exp Exp   [strict(1)]

endkm
