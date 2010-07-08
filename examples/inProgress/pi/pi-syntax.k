kmod PI-SYNTAX is including PL-ID
  syntax Action ::= send Id on Id [prec 0 latex "\overline{#2}\langle{#1}\rangle"] 
                  | receive Id on Id [prec 0 latex "{#2}({#1})"] 
  syntax Proc ::= Proc || Proc [prec 110 latex "{#1}\mid{#2}"]
                | Proc + Proc [prec 105 latex "{#1}+{#2}"]
                | new Id . Proc [prec 100 latex "(\nu {#1}){#2}"]
                | replicate Proc [prec 105 latex "!"]
                | ()
                | Action . Proc [prec 90 latex "{#1}.{#2}"]
endkm