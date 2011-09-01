load .k/imp
module SUMIO  imports IMP-SYNTAX
syntax #Id ::= n | s 
syntax Stmt ::= sumio

macro sumio = (
     n=read("Add numbers up to? n=");
     s=0;
     while not(n<=0) do (
       s=s+n;
       n=n+-1;
     )
     writeln(s);
)

end module
