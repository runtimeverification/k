//1.1

module EASY
//@4.5  syntax K ::= #String
//@4.3             | "write" "(" K ")" ";"

/*@1.2
  configuration 
    <k> $PGM:K </k>
*/

//1.2
/*@4.2
  configuration 
    <k> $PGM:K </k>
    <out> .List </out>
*/  

  rule 
    <k> write(Str:#String); => . ...</k>
    <out>... . => ListItem(Str) </out>

//2.1
  syntax K ::= K K

//2.2
  rule
    K1:K K2:K => K1 ~> K2

//3.1
//@4.4  syntax K ::= K "+" K

//3.2
  rule 
    Str1:#String + Str2:#String => Str1 +String Str2

//4.1
  syntax K ::= #Id
             | "var" K "=" K ";"

//4.2
/*@5.2
  configuration 
    <k> $PGM:K </k>
    <out> .List </out>
    <env> .Map </env>
*/

  rule
    <k> var X:#Id = Str:#String ; => . ...</k>
    <env>... . => X |-> Str ...</k>

//4.3
   syntax K ::= "write" "(" K ")" ";" [strict]

//4.4
  syntax K ::= K "+" K [strict]

//4.5
  syntax KResult ::= #String
  
//4.6
  rule
    <k> X:#Id => R ...</k>
    <env>... X |-> R:KResult ...</env>

//4.7 mabe revisit eveything and add strict and KResult

//5.1
   syntax K ::= "function" K "(" K ")" "{" K "}"
              | "return" K ";" [strict]
              | "call" K "(" K ")" [strict(2)]

//5.2
/*@5.3
  configuration 
    <k> $PGM:K </k>
    <out> .List </out>
    <env> .Map </env>
    <procs> .Map </procs>
*/

/*@5.7
  rule 
    <k> function X:#Id ( Xs:K ) { K:K } => . ...</k>
    <procs>... . => X |->  function X ( Xs ) { K } ...</procs>
*/

//5.3
/*@6.2
  configuration 
    <k> $PGM:K </k>
    <out> .List </out>
    <env> .Map </env>
    <procs> .Map </procs>
    <fstack> .List </fstack>
*/

  syntax K ::= "frame" "(" K "," Map ")"

  rule
    <k> call X:#Id ( Rs:KResult ) ~> K:K => bindTo(Xs,Rs) ~> Body </k>
    <env> Env:Map => . </env>
    <procs>... X |->  function X ( Xs:K ) { Body:K } ...</procs>
    <fstack>... . => ListItem(frame(K,Env)) </fstack>

  syntax K ::= "bindTo" "(" K "," K ")"

//5.4
  rule 
    <k> bindTo(X:#Id,R:KResult) => . ...</k>
    <env>... . => X |-> R ...</env>

//5.5
  rule 
    <k> return R:KResult; ~> _ => R ~> K </k>
    <env> _ => Env </env>
    <fstack>... ListItem(frame(K,Env)) => . </fstack>

//5.6
  syntax K ::= K ; [strict]

//5.7
  rule 
    <k> function X:#Id ( Xs:K ) { K:K } => . ...</k>
    <procs>... . => X |->  function X ( Xs ) { K ~> return "";} ...</procs>

//5.8
  rule R:KResult; => .

//6.1
  syntax K ::= "spawn" K "(" K ")" ; [strict(2)]
  
//6.2
  configuration 
    <thread multiplicity="*">
      <k> $PGM:K </k>
      <env> .Map </env>
      <fstack> .List </fstack>
    </thread>
    <out> .List </out>
    <procs> .Map </procs>

  rule
    <k> spawn X:#Id(R:KResult); => . ...</k>
    (. => <thread>... <k> call X(R); </k> ...</thread>)

//6.3
  rule
    <thread>... <k> . </k> ...</thread> => .

//7.1
  syntax K ::= K "-" K [strict]
             | K "*" K [strict]
             | K "<=" K [strict]
             | "if" "(" K ")" "then" K "else" K "fi" ";"  [strict(1)]

  syntax KResult ::= #Int | #Bool

end module

