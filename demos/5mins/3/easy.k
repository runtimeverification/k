module EASY 
  syntax K ::= print ( #String );

//@1  configuration <k> $PGM:K </k>

//1
  configuration <k> $PGM:K </k> <out> .List </out>

//@4  rule <k> print(S:#String); => . </k> <out> . => ListItem(S) </out>


//2
  syntax K ::= K K

//3
  rule K1:K K2:K => K1 ~> K2

//4
  rule <k> print(S:#String); => . ...</k> <out>... . => ListItem(S) </out>

//5
  syntax K ::= K + K  
  rule S1:#String + S2:#String => S1 +String S2
end module
