kmod SORT is including K + PL-INT
  configuration <sortme> .List </sortme>
  syntax K ::= Int 
  rule <sortme_> ListItem((I:Int => J)) _ ListItem((J:Int => I)) <_/sortme>
    if I >Int J
endkm
