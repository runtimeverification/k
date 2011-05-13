require cink-syntax

kmod CINK-PROGRAMS is including CINK-SYNTAX 
  syntax Pgm ::= pSum | pCollatz | pFoo | pSwap | pSumArr 

  syntax Id ::= a | b | c | d | e | i | l 
          | limit | nr | nn | n | p | q | r | s | steps | t | t1 | t2 | x | y | z 
          | swap | aux | sum

  macro pSum = 
    int main() {
         int n = 1000 ;
	 int s = 0 ;
         int i = n ;
         while (!(i <= 0)) {
           s = s + i ;
           i = i - 1 ;
         } 
         printf("%d;",s);
    }

  macro pCollatz = 
    int main() {
         int limit = 10 ;
         int steps = 0 ; int nr = 2 ;
         int n; int d; int nn;
         while (nr <= limit) {
           n = nr ; nr = nr + 1 ;
           while (!(n <= 1)) {
             steps = steps + 1 ;
	     d = 0 ;
             nn = 2 ;
             while (nn <= n) {
               d = d + 1 ;
               nn = nn + 2 ;
             }
             if (nn <= (n + 1)) n = n + n + n + 1 ; else n = d ;
           }
         } 
         printf("%d;",steps);
  } 

  macro pFoo =
    int t()
    {
       return 1;
    }

    int t1()
    {
       int a = 2;
       return a;
    }

    int t2()
    {
       int a = 3;
       return a;
    }

    void main() {
       int b;
       b = t() + t1() + t2();
       printf("%d;", b);
    }

 macro pSwap =
   void swap(int *x, int *y)
   {
      int aux = *x;
      *x = *y ;
      *y = aux;
      //breakpoint;
   }

  void main()
  {
    int *a = (int *) malloc(1*sizeof(int));
    int *b = (int *) malloc(1*sizeof(int));
    *a = 17;
    *b = 15;
    swap(a, b);
    printf("%d;", *a);
    printf("%d;", *b); 
    free(a);
    free(b);
  }

 macro pSumArr =
   int sum(int *a, int n)
   {
     int s = 0;
     int i = 0;
     while (i <= n)
     {  
        s = s + a[i];
        i = i + 1;
     }
     return s;
   }
   void main()
   {
      int n;
      int b[20];
      scanf("%d", & n);
      int i=0;
breakpoint;
      while (i < n)
      {
         b[i] = i; 
         i = i + 1; 
      }
      printf("%d;", sum(b, n));
   }
endkm

