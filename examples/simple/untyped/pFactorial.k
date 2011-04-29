kmod PFACTORIAL is
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
endkm
