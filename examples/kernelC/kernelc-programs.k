kmod KERNELC-PROGRAMS is including KERNELC-SYNTAX 
  syntax Pgm ::= pSum | pCollatz | pBufferOverflow | pSimpTest  | pStrErr | pStrTest
               | pAllocateBadPrint | pAllocatePrintReversePrintFree | pAllocatePrintFree
  syntax StmtList ::= pPrint  | pAllocateLoop | pAllocateGood | pAllocateBad | pReverse
                    | pFree | pStrLen | pStrCpy | pStrPrint | pStrDup | pString | pString2
  syntax Id ::= n | o | p | q | a | b | d | i | x | y | z | s | nr | nn | steps | limit

  macro pSum = 
    #include<stdio.h>
    #include<stdlib.h>
    void main(void) {
         n = 1000 ;
	 s = 0 ;
         i = n ;
         while (!(i <= 0)) {
           s = s + i ;
           i = i - 1 ;
         } 
         printf("%d;",s);
    }

  macro pCollatz = 
    #include<stdio.h>
    #include<stdlib.h>
    void main(void) {
         limit = 10 ;
         steps = 0 ; nr = 2 ;
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

  macro pPrint =
 p = a ;
 while (p) {
  printf("%d;",* p);
  p = * (p + 1) ;
 }
 
  macro pAllocateLoop = 
 n = 0 ;
 while (n != a) {
  q = malloc(2) ;
  * q = n ;
  * (q + 1) = p ;
  p = q ;
  n = n + 1 ;
 }
 o = p ;

  macro pAllocateGood = 
 p = null ;
 pAllocateLoop

  macro pAllocateBad = 
 p = malloc(2) ;
 pAllocateLoop

  macro pReverse = 
 p = a ;
 if (p) {
  x = *(p + 1) ;
  *(p + 1) = null ;
  while (x) {
   y = *(x + 1);
   *(x + 1) = p ;
   p = x ;
   x = y ;
  }
 }
 o = p ;

  macro pFree =
 p = a ;
 while (p) {
  q = * (p + 1) ;
  free(p) ;
  p = q ;
 }

  macro pStrLen =
   o = 0 ;
   while (* a) {
     a = a + 1 ;
     o = o + 1 ;
   }

  macro pStrCpy =
   while (* a) {
     * b = * a ;
     a = a + 1 ;
     b = b + 1 ;
   }
   * b = 0 ;

  macro pStrDup =
    b = a ;
    pStrLen 
    o = malloc(o + 1) ;
    a = b ;
    b = o ;
    pStrCpy
    * b = 0 ;

  macro pString =
    o = malloc(5) ;
    * o = 1 ;
    * (o + 1) = 2 ;
    * (o + 2) = 3 ;
    * (o + 3) = 4 ;
    * (o + 4) = 0 ;

  macro pString2 = 
    o = malloc(7) ;
    * o = 5 ;
    * (o + 1) = 6 ;
    * (o + 2) = 7 ;
    * (o + 3) = 8 ;
    * (o + 4) = 9 ;
    * (o + 5) = 10 ;
    * (o + 6) = 0 ;

  macro pBufferOverflow =
    #include<stdio.h>
    #include<stdlib.h>
    void main(void) {
      pString
      a = x = o ;
      pStrPrint
      pString
      a = y = o ;
      pStrPrint
      pString2
      a = z = o ;
      pStrPrint
      a = z ; b = x ;
      pStrCpy
      printf("%d;", -1) ; a = x ; pStrPrint
      printf("%d;", -1) ; a = y ; pStrPrint
      printf("%d;", -1) ; a = z ; pStrPrint      
    }

  
  macro pStrPrint =
   while (* a) {
     printf("%d;",* a);
     a = a + 1 ;
   }

  macro pStrTest  = 
    #include<stdio.h>
    #include<stdlib.h>
    void main(void) {
   pString 
   x = o ; 
   a = x ; 
   pStrDup 
   y = o ; 
   a = y ; 
   pStrPrint 
   free(x);
   free(y);
}

  macro pStrErr =
    #include<stdio.h>
    #include<stdlib.h>
    void main(void) {
   pString
   x = o ;
   pString
   y = o ;
   * (y - 1) = 5 ;
   a = x ;
   pStrPrint
   free(x);
   free(y);
}

macro pAllocatePrintFree =
    #include<stdio.h>
    #include<stdlib.h>
    void main(void) {
a = 5 ; pAllocateGood a = o ; pPrint pFree 
} 

macro pAllocatePrintReversePrintFree =
    #include<stdio.h>
    #include<stdlib.h>
    void main(void) {
a = 7 ; pAllocateGood a = o ; pPrint pReverse a = o ; pPrint pFree
} 

macro pAllocateBadPrint =
    #include<stdio.h>
    #include<stdlib.h>
    void main(void) {
a = 2 ; pAllocateBad a = o ; pPrint 
} 

macro pSimpTest =
 #include<stdio.h>
    #include<stdlib.h>
    void main(void) {
x = malloc(3) ;
y = malloc(4) ;
if (x == 0 && y == 1) z = 1 ;
else z = x + y ;
printf("%d;",z) ;
} 

endkm

