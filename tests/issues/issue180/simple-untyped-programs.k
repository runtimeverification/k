module SIMPLE-UNTYPED-PROGRAMS imports SIMPLE-UNTYPED-SYNTAX

  syntax Id ::=  x

  syntax Stmts ::= pTestND


  macro pTestND =
      function main() {
        var x[5];
        write(++(x[x[1]]));
      }

end module
