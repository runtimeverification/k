module SORT is
  configuration <sortme> .List </sortme>
  syntax K ::= #Int 
  rule <sortme>... ListItem((I:#Int => J)) _ ListItem((J:#Int => I)) 
      ...</sortme>
    when I >Int J
end module
