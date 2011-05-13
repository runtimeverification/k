
load cink-compiled
load cink-syntax

kmod SWAP is including CINK-SYNTAX
	syntax Id ::= a | aux | b | main | swap | x | y 

	syntax Pgm ::= swap

	macro swap = 
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
 


endkm
