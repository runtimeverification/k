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
             | "var" K "=" K ";" [strict(2)]

//4.2
/*@5.2
  configuration 
    <k> $PGM:K </k>
    <out> .List </out>
    <env> .Map </env>
*/

/*@8.2
  rule
    <k> var X:#Id = Str:#String ; => . ...</k>
    <env>... . => X |-> Str ...</k>
*/

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
    <functions> .Bag </functions>
*/

/*@5.7
  rule 
    <k> function X:#Id ( Xs:K ) { K:K } => . ...</k>
    <functions>... . => BagItem(function X ( Xs ) { K }) ...</functions>
*/

//5.3
/*@6.2
  configuration 
    <k> $PGM:K </k>
    <out> .List </out>
    <env> .Map </env>
    <functions> .Bag </functions>
    <fstack> .List </fstack>
*/

  syntax K ::= "frame" "(" K "," Map ")"

  rule
    <k> call X:#Id ( Rs:KResult ) ~> K:K => bindTo(Xs,Rs) ~> Body </k>
    <env> Env:Map => . </env>
    <functions>... BagItem(function X ( Xs:K ) { Body:K }) ...</functions>
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
    <functions>... . => BagItem(function X ( Xs ) { K ~> return "";}) ...</functions>

//5.8
  rule R:KResult; => .

//6.1
  syntax K ::= "spawn" K "(" K ")" ; [strict(2)]
  
//6.2
/*@8.3
  configuration 
    <thread multiplicity="*">
      <k> $PGM:K </k>
      <env> .Map </env>
      <fstack> .List </fstack>
    </thread>
    <out> .List </out>
    <functions> .Bag </functions>
*/

  rule
    <k> spawn X:#Id(R:KResult); => . ...</k>
    (. => <thread>... <k> call X(R); </k> ...</thread>)

//6.3
  rule
    <thread>... <k> .K </k> ...</thread> => .

//7.1
  syntax K ::= K "-" K [strict]
             | K "*" K [strict]
             | K "<=" K [strict]
             | "if" K "{" K "}" "else" "{" K "}"  [strict(1)]

  syntax KResult ::= #Int | #Bool

//7.2
  rule 
    I1:#Int <= I2:#Int => I1 <=Int I2

//7.3
  rule
    if (true) { K:K } else { _ } => K
  rule
    if (false) { _ } else { K:K } => K

//7.4
  rule
    I1:#Int - I2:#Int => I1 +Int (-Int I2)

//7.5
  rule
    I1:#Int * I2:#Int => I1 *Int I2

//7.6
  rule
    write(I:#Int); => write(Int2String(I));

//8.1
  syntax K ::= "new" "BlockingQueue" "(" K ")" [strict]
             | "put" "(" K "," K ")" ";" [strict]
             | "take" "(" K "," K ")" [strict]
//@8.4             | K "," K [strict]

//8.2
  rule
    <k> var X:#Id = R:KResult ; => . ...</k>
    <env>... . => X |-> R ...</k>

//8.3
  configuration 
    <thread multiplicity="*">
      <k> $PGM:K </k>
      <env> .Map </env>
      <fstack> .List </fstack>
    </thread>
    <out> .List </out>
    <functions> .Bag </functions>
    <queues> 
      <queue multiplicity="*">
        <id> 0 </id>
        <data> .List </data>
        <free> 0 </free>
      </queue>
      <qid> 0 </qid>
    </queues>

  rule 
    <k> new BlockingQueue(Size:#Int) => N ...</k>
    <qid> N:#Int => N +Int 1 </qid>
    (. => <queue>... <id> N </id> <free> Size </free> ...</queue>)

//8.4
  syntax K ::= K "," K [strict hybrid]

end module

