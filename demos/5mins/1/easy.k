module EASY 
  syntax K ::= print ( #String );

//@1  configuration <k> $PGM:K </k>

//1
  configuration <k> $PGM:K </k> <out> .List </out>

  rule <k> print(S:#String); => . </k> <out> . => ListItem(S) </out>
end module
