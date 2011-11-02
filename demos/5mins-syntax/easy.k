//1.1

module EASY
//@4.5  syntax Exp ::= #String
//@4.3  syntax Stmt ::= "write" "(" Exp ")" ";"

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
  syntax Stmt ::= Stmt Stmt

//2.2
  rule St1:Stmt St2:Stmt 
    => St1 ~> St2

//3.1
//@4.4  syntax Exp ::= Exp "+" Exp

//3.2
  rule Str1:#String + Str2:#String 
    => Str1 +String Str2

//4.1
  syntax Exp ::= #Id
  syntax Stmt ::= "var" #Id "=" Exp ";" [strict(2)]

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
   syntax Stmt ::= "write" "(" Exp ")" ";" [strict]

//4.4
  syntax Exp ::= Exp "+" Exp [strict]

//4.5
  syntax Exp ::= Val 
  syntax Val ::= #String
  syntax KResult ::= Val
  
//4.6
  rule
    <k> X:#Id => V ...</k>
    <env>... X |-> V:Val ...</env>

//4.7 maybe revisit eveything and add strict and KResult

//5.1
   syntax Stmt ::= "function" #Id "(" Ids ")" "{" Stmt "}"
                 | "return" Exp ";" [strict]
   syntax Exp ::= "call" #Id "(" Exps ")" [strict(2)]
   syntax Ids ::= List{#Id,","}
   syntax Exps ::= List{Exp,","}

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
    <k> function X:#Id ( Xs:Ids ) { Body:Stmt } => . ...</k>
    <functions>... . => BagItem(function X ( Xs ) { Body }) ...</functions>
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
  syntax Vals ::= List{Val,","}

  rule
    <k> call X:#Id ( Vs:Vals ) ~> K:K => bindTo(Xs,Vs) ~> Body </k>
    <env> Env:Map => . </env>
    <functions>... BagItem(function X ( Xs:Ids ) { Body:Stmt }) ...</functions>
    <fstack>... . => ListItem(frame(K,Env)) </fstack>

  syntax K ::= "bindTo" "(" Ids "," Vals ")"

  rule 
    <k> bindTo((X:#Id,Xs:Ids => Xs),(V:Val,Vs:Vals => Vs)) ...</k>
    <env>... . => X |-> V ...</env>

//5.4
  rule bindTo(,)
    => .
    

//5.5
  rule 
    <k> return V:Val; ~> _ => V ~> K </k>
    <env> _ => Env </env>
    <fstack>... ListItem(frame(K,Env)) => . </fstack>

//5.6
  syntax Stmt ::= Exp ";" [strict]

//5.7
  rule 
    <k> function X:#Id ( Xs:Ids ) { Body:Stmt } => . ...</k>
    <functions>... . => BagItem(function X ( Xs ) { Body return "";}) ...</functions>

//5.8
  rule V:Val; 
    => .

//6.1
  syntax Stmt ::= "spawn" #Id "(" Exps ")" ; [strict(2)]
  
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
    <k> spawn X:#Id(Vs:Vals); => . ...</k>
    (. => <thread>... <k> call X(Vs); </k> ...</thread>)

//6.3
  rule <thread>... <k> .K </k> ...</thread> 
    => .

//7.1
  syntax Exp ::= Exp "-" Exp [strict]
             | Exp "*" Exp [strict]
             | Exp "<=" Exp [strict]
  syntax Stmt ::= "if" Exp "{" Stmt "}" "else" "{" Stmt "}"  [strict(1)]

  syntax Val ::= #Int | #Bool

//7.2
  rule I1:#Int <= I2:#Int 
    => I1 <=Int I2

//7.3
  rule if (true) { St:Stmt } else { _ } 
    => St
  rule if (false) { _ } else { St:Stmt } 
    => St

//7.4
  rule I1:#Int - I2:#Int 
    => I1 +Int (-Int I2)

//7.5
  rule I1:#Int * I2:#Int 
    => I1 *Int I2

//7.6
  rule write(I:#Int); 
    => write(Int2String(I));

//8.1
  syntax Exp ::= "new" "BlockingQueue" "(" Exp ")" [strict]
             | "take" "(" Exp ")" [strict]
  syntax Stmt ::= "put" "(" Exp "," Exp ")" ";" [strict]

//8.2
  rule
    <k> var X:#Id = V:Val ; => . ...</k>
    <env>... . => X |-> V ...</k>

//8.3
/*@8.5
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
*/

  rule 
    <k> new BlockingQueue(Size:#Int) => N ...</k>
    <qid> N:#Int => N +Int 1 </qid>
    (. => <queue>... <id> N </id> <free> Size </free> ...</queue>)

//8.4
  rule 
    <k> put(N:#Int, V:Val); => . ...</k>
    <id> N </id>
    <data>... . => ListItem(V) </data>
    <free> Size:#Int => Size +Int -1 </free>
    if Size >Int 0 [transition]

  rule 
    <k> take(N:#Int) => V ...</k>
    <id> N </id>
    <data> ListItem(V:Val) => . ...</data>
    <free> Size:#Int => Size +Int 1 </free> [transition]

//8.5
  configuration 
    <thread multiplicity="*">
      <k> $PGM:K </k>
      <env> .Map </env>
      <fstack> .List </fstack>
    </thread>
    <in stream="stdin"> .List </in>
    <out stream="stdout"> .List </out>
    <functions> .Bag </functions>
    <queues> 
      <queue multiplicity="*">
        <id> 0 </id>
        <data> .List </data>
        <free> 0 </free>
      </queue>
      <qid> 0 </qid>
    </queues>

  syntax Exp ::= read
  
  rule
    <k> read => I ...</k>
    <in> ListItem(I:#Int) => . ...</in>
end module

