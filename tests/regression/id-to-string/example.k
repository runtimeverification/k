
module EXAMPLE-SYNTAX
  syntax K ::= "print" "(" Id ")"
  syntax Id ::= "ala" | "bala" | "portocala"
end module 

module EXAMPLE
  imports EXAMPLE-SYNTAX
  configuration <k> $PGM:K </k> <out stream="stdout"> .List </out> 

  rule <k> print(X:Id) => . ...</k> 
       <out>... .List => ListItem(Id2String(X)) </out>
end module
