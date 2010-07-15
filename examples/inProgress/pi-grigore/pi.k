load ../../../k-prelude

kmod SUBSTITUTION is  including PL-ID + K
  syntax Bool ::= fresh ( Id )
  syntax Bag ::= Bag [ Id / Id ] 
endkm

kmod PI is including SUBSTITUTION
  syntax Action ::= send Id on Id [prec 0 latex "\overline{#2}\langle{#1}\rangle"] 
                  | receive Id on Id [prec 0 latex "{#2}({#1})"] 
  syntax BagItem ::= new Id . Bag [prec 100 latex "(\nu {#1}){#2}"]
                   | replicate Bag [prec 105 latex "!"]
                   | Action . Bag [prec 90 latex "{#1}.{#2}"]
                
  configuration <par> <sum*> .Bag </sum*> </par>
  

  rule [comm] : <sum> _ (send X:Id on C:Id . P:Bag) => P </sum>
       <sum> _ (receive Y:Id on C . Q) => Q[X/Y] </sum>

  rule [!comm] : <sum> _ (send X on C . P)  => P </sum>
                 <sum> (_ => .) (replicate receive Y on C . Q:Bag) </sum> 
                 (. => <sum> Q[X/Y] </sum>)
  
  rule <par> R <sum> Q (new X . P) </sum> </par> => (new Y . <par> R:Bag <sum> Q (P[Y/X]) </sum> </par>)  if fresh(Y) [structural]
  
  rule <sum> .Bag </sum> => . [structural]
  rule <par> .Bag </par> => . [structural]  
  rule <sum> <par> P </par> </sum> => P [structural]
  rule <sum> <sum> P </sum> => P </sum> [structural]
endkm