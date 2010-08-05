kmod SORT is including K + PL-INT
  configuration <sortme> .List </sortme>
  syntax K ::= Int 
  rule <sortme_> ListItem((x:Int => y)) _ ListItem((y:Int => x)) <_/sortme>
    if x >Int y
endkm
