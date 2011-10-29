module EASY 
//@3.4  syntax K ::= print ( K );

//@1  configuration <k> $PGM:K </k>

//1
/*3.2  configuration 
    <k> $PGM:K </k> 
    <out> .List </out>
*/

//@2  rule <k> print(S:#String); => . </k> <out> . => ListItem(S) </out>


//1.1
  syntax K ::= K K

//1.2
  rule K1:K K2:K => K1 ~> K2

//2
  rule 
    <k> print(S:#String); => . ...</k> 
    <out>... . => ListItem(S) </out>

//3
//@3.5  syntax K ::= K + K  
  rule S1:#String + S2:#String => S1 +String S2

//3.1
  syntax K ::= #Id
             | var K ;
             | K = K ;
//3.2
  configuration 
    <k> $PGM:K </k> 
    <env> .Map </env> 
    <out> .List </out>

  rule 
    <k> var X:#Id ; => . ...</k> 
    <env>... .Map => X |-> "" ...</env>

//3.3
  rule 
    <k> X:#Id = S:#String ; => . ...</k>
    <env>... X |-> (_ => S) ...</env>   

//3.4
  syntax K ::= print ( K ); [strict]

//3.5
  syntax K ::= K + K [strict] 

//3.6
  syntax KResult ::= #String

//4
  rule
    <k> X:#Id => K:K ...</k>
    <env>... X |-> K ...</env>
end module
