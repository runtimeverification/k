module EASY-SYNTAX
//0.1
//@2.1  syntax Stmt ::= "write" ( #String ) 
//1.1
  syntax Stmt ::= Stmt ";" Stmt   // statement sequencing
//2.1 
  syntax Stmt ::= "write" ( Exp ) 
  syntax Exp ::= #String 
               | Exp + Exp
end module

//0.2

module EASY imports EASY-SYNTAX
/*@1  configuration 
    <k> $PGM:K </k>
*/

//1
  configuration 
    <k> $PGM:K </k> 
    <out> .List </out>

  rule 
    <k> write(S:#String) => . ...</k> 
    <out>... . => ListItem(S) </out>

//2
  rule 
    St1:Stmt ;  St2:Stmt => St1 ~> St2

//3
  rule
    S1:#String + S2:#String => S1 +String S2
end module

