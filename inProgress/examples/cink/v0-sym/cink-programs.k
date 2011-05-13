require cink-syntax

kmod CINK-PROGRAMS is including CINK-SYNTAX 
  syntax Pgm ::= pFact | pFoo1 | pFoo2 | pFoo3
  syntax Id ::= fact | n | i | result | f 

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

  macro pFoo1 =
    int f() { return -1; }
    int main() {
       int i = 1;
       if (i > 0)
          while (i > 0) { i = i+1+f(); }
       else
          i = 0;
    }

  macro pFoo2 =
    int main() {
       int i;
       scanf("%d", &i);
       while (i > 0) { 
          if (0 > i)
             i = i+1; 
          else
             i = 1;
       }
    }

  macro pFoo3 =
    int main() {
       int i;
       scanf("%d", &i);
       while (i > 0) { i = i+1; }
    }
endkm

