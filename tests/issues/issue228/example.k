module TEST-SYNTAX
  syntax Type ::= "int"
  syntax Types ::= List{Type,","}

  syntax Id ::= "a" | "b"
  syntax Ids ::= List{Id,","}

  syntax IdType ::= Id ":" Type [prec 0]
  syntax IdTypes ::= List{IdType,","}
end module

module TESTS imports TEST-SYNTAX
  syntax IdTypes ::= "start" 
  syntax Ids ::= "result"
  macro start = a : int, b : int
  macro result = a, b
end module

module ISSUE
  imports TESTS
  syntax KResult ::= Type

  syntax Ids ::= "ids" IdTypes

  rule ids ((X:Id : T:Type), XTs:IdTypes) => X, ids XTs
  rule ids .IdTypes => .Ids

  configuration <k> .K </k>

  syntax K ::= "equal" "(" K "," K ")" | "passed" | "test"
  rule equal(X,X) => passed
  rule test => equal(ids start,result)


end module
