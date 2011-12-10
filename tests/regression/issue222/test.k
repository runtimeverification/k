module TEST

  syntax Test ::= "($" Test "$)" | "blah"
  configuration <T><k> $PGM:Test </k></T>
  
end module
