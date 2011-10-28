module EASY 
  syntax K ::= print ( #String );

//@1  configuration <k> $PGM:K </k>

//1
  configuration <k> $PGM:K </k> <out> .List </out>

//@2  rule <k> print(S:#String); => . </k> <out> . => ListItem(S) </out>


//1.1
  syntax K ::= K K

//1.2
  rule K1:K K2:K => K1 ~> K2

//2
  rule <k> print(S:#String); => . ...</k> <out>... . => ListItem(S) </out>

//3
  syntax K ::= K + K  
  rule S1:#String + S2:#String => S1 +String S2
end module
