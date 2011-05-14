in simple-untyped-compiled
in simple-untyped-syntax

kmod PFACTORIAL is including SIMPLE-UNTYPED-SYNTAX
  macro pFactorial =
       var x;

       function f(y) {
         var t=1;
         for i = 1 to y do
           t = t*i;
         return t;
       }

       function main() {
         x = 5;
         write(f(f(x)));
       }

  syntax Stmts ::= pFactorial
  syntax Id ::= x | f | y | i | t
endkm
