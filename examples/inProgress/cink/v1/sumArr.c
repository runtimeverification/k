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

