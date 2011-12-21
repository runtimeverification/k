kmod DIJKSTRA is including NAT-INF 
  configuration <graph> .Set </graph> <shortest> .Map </shortest>

  syntax Edge ::= #Id - #Nat -> #Id [latex "{#1}\xrightarrow{{#2}}{#3}"]

  syntax K ::= #Id 
  syntax SetItem ::= Edge
  
  rule <graph>... x1 -w:#Nat-> x2 ...</graph> 
       <shortest>... 
          x1:#Id |-> c1:#Nat  x2:#Id |-> (c2:#NatInf => c1 +Nat w) 
       ...</shortest>
    when w +Nat c1 <Nat c2
endkm
