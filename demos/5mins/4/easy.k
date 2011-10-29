module EASY-SYNTAX
//0.1
//@2.1  syntax Stmt ::= "write" ( #String ) 
//1.1
  syntax Stmt ::= Stmt ";" Stmt   // statement sequencing
//2.1 
//@3.4  syntax Stmt ::= "write" ( Exp ) 
  syntax Exp ::= #String 
//@3.5               | Exp + Exp
//3.1
  syntax Exp ::= #Id
  syntax Stmt ::= var #Id 
                | #Id := Exp
//3.4
  syntax Stmt ::= "write" ( Exp ) [strict]
//3.5
  syntax Exp ::= Exp + Exp [strict]
end module

//0.2

module EASY imports EASY-SYNTAX
/*@1  configuration 
    <k> $PGM:K </k>
*/

//1
/*@3.2  configuration 
    <k> $PGM:K </k> 
    <out> .List </out>
*/

  rule 
    <k> write(S:#String) => . ...</k> 
    <out>... . => ListItem(S) </out>

//2
  rule 
    St1:Stmt ;  St2:Stmt => St1 ~> St2

//3
  rule
    S1:#String + S2:#String => S1 +String S2

//3.2
  configuration 
    <k> $PGM:K </k> 
    <env> .Map </env> 
    <out> .List </out>

  rule 
    <k> var X:#Id => . ...</k> 
    <env>... .Map => X |-> "" ...</env>

//3.3
  rule 
    <k> X:#Id := S:#String => . ...</k>
    <env>... X |-> (_ => S) ...</env>   

//3.6
  syntax KResult ::= #String

//4
  rule
    <k> X:#Id => K:K ...</k>
    <env>... X |-> K ...</env>
end module

