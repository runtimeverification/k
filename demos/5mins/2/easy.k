module EASY 
  syntax K ::= print ( #String );

//@1  configuration <k> $PGM:K </k>

//1
  configuration <k> $PGM:K </k> <out> .List </out>

//@3  rule <k> print(S:#String); => . </k> <out> . => ListItem(S) </out>


  syntax K ::= K K

//2
  rule K1:K K2:K => K1 ~> K2


  rule <k> print(S:#String); => . ...</k> <out>... . => ListItem(S) </out>
  
end module
