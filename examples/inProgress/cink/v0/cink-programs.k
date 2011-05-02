require cink-syntax

kmod CINK-PROGRAMS is including CINK-SYNTAX 
  syntax Pgm ::= pFact 
  syntax Id ::= fact | n | i | result


  macro pFact =
    int fact(int n) {
          int result = 1;
          while (n > 0) {
            result = n * result;
            n = n - 1;
          }
          return result;
        }
    int main() {
         int n;
         scanf("%d", &n);
         printf("%d;",fact(n));
    }

endkm

