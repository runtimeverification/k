module HALT
  syntax K ::= halt K [strict]
  rule <k>halt(V:KResult)~>_ => V</k> 
end module
