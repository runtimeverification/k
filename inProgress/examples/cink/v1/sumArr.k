
load cink-compiled
load cink-syntax

kmod SUMARR is including CINK-SYNTAX
	syntax Id ::= a | b | i | main | n | s | sum 

	syntax Pgm ::= sumArr

	macro sumArr = 
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
    //   breakpoint;
       while (i < n)
       {
          b[i] = i; 
          i = i + 1; 
       }
       printf("%d;", sum(b, n));
    }
 


endkm
