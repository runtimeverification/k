module RETURN-CODE
  imports INT

  configuration
    <k> $PGM:Foo </k>
    <rc exit=""> 0 </rc>

  syntax Foo ::= foo(Int)
  rule
    <k> foo(I) => .K ...</k>
    <rc> _ => I </rc>
endmodule
