module EASY-SYNTAX
//0.1
  syntax Stmt ::= "write" "(" #String ")" 
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
end module

