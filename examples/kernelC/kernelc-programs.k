kmod KERNELC-PROGRAMS is including KERNELC-SYNTAX 
  syntax Pgm ::= pSum | pCollatz | pBufferOverflow | pSimpTest  | pStrErr | pStrTest
               | pAllocateBadPrint | pAllocatePrintReversePrintFree | pAllocatePrintFree
  syntax Stmt ::= pPrint  | pAllocateLoop | pAllocateGood | pAllocateBad | pReverse
                    | pFree | pStrLen | pStrCpy | pStrPrint | pStrDup | pString | pString2
  syntax Id ::= a | b | c | d | e | i | l | limit | nr | nn | n | p | q | r | s | steps | t | x | y | z 

  syntax Id ::= print | allocateLoop | reverse | quickSort

  macro pSum = 
    #include<stdio.h>
    #include<stdlib.h>
    void main() {
         int i,n,s;
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
    void main() {
         int limit,steps,nr,n,d,nn;
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
void print(a) {
  int p;
 p = a ;
 while (p) {
  printf("%d;",* p);
  p = * (p + 1) ;
 }
}
 
  macro pAllocateLoop = 
int allocateLoop(a,p) {
 int n,q ;
 n = 0 ;
 while (n != a) {
  q = malloc(2) ;
  * q = n ;
  * (q + 1) = p ;
  p = q ;
  n = n + 1 ;
 }
 return p ;
}

---  macro pAllocateGood = allocateLoop(a,null) ;

---  macro pAllocateBad = allocateLoop(a, malloc(2), o) ;

  macro pReverse = int reverse(p) {
  int x,y;
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
 return p ;
}

  macro pFree = void freeList(p) {
int q;
 while (p) {
  q = * (p + 1) ;
  free(p) ;
  p = q ;
 }
}

  macro pStrLen = int strlen(a) {
   int l ; l = 0;
   while(* a) {
     a = a + 1;
     l = l + 1;
   }
   return l;
}

  macro pStrCpy = void strcpy(a,b) {
   while (* a) {
     * b = * a ;
     a = a + 1 ;
     b = b + 1 ;
   }
   * b = 0 ;
}

  macro pStrDup = int strdup(a) {
    int p;
    p = malloc(strlen(a)+1) ;
    strcpy(a,p);
    return p;
  }

  macro pString = int string() {
    int p;
    p = malloc(5) ;
    * p = 1 ;
    * (p + 1) = 2 ;
    * (p + 2) = 3 ;
    * (p + 3) = 4 ;
    * (p + 4) = 0 ;
    return p;
}

  macro pString2 =  int string2() {
    int p;
    p = malloc(7) ;
    * p = 5 ;
    * (p + 1) = 6 ;
    * (p + 2) = 7 ;
    * (p + 3) = 8 ;
    * (p + 4) = 9 ;
    * (p + 5) = 10 ;
    * (p + 6) = 0 ;
    return p;
}

  macro pBufferOverflow =
    #include<stdio.h>
    #include<stdlib.h>
    pString
    pString2
    pStrCpy
    pStrPrint
    void main() {
      x = string();
      strprint(x);
      y = string();
      strprint(y);
      z = string2();
      strprint(z);
      strcpy(z,x);
      printf("%d;", -1) ; strprint(x);
      printf("%d;", -1) ; strprint(y);
      printf("%d;", -1) ; strprint(z);
    }

  
  macro pStrPrint =  void strprint(a) {
   while (* a) {
     printf("%d;",* a);
     a = a + 1 ;
   }
}

  macro pStrTest  = 
    #include<stdio.h>
    #include<stdlib.h>
    pString
    pStrCpy
    pStrLen
    pStrDup
    pStrPrint
    void main() {
   x = string(); 
   y = strdup(x);
   strprint(y);
   free(x);
   free(y);
}

syntax Id ::= strdup | strprint | strcpy | strlen | string | string2 | freeList 

  macro pStrErr =
    #include<stdio.h>
    #include<stdlib.h>
   pString
   pStrPrint
    void main() {
   x = string();
   y = string();
   * (y - 1) = 5 ;
   strprint(x);
   free(x);
   free(y);
}

macro pAllocatePrintFree =
    #include<stdio.h>
    #include<stdlib.h>
    pAllocateLoop
    pPrint
    void main() {
      int a ; a = allocateLoop(5,null); print(a); free(a);
    } 

macro pAllocatePrintReversePrintFree =
    #include<stdio.h>
    #include<stdlib.h>
    pAllocateLoop
    pPrint
    pReverse
    void main() {
      int a ; a = allocateLoop(7,null); print(a); a = reverse(a); print(a); free(a);
    } 

macro pAllocateBadPrint =
    #include<stdio.h>
    #include<stdlib.h>
    pAllocateLoop
    pPrint
    void main() {
      int a ; a = allocateLoop(2,malloc(2)); print(a); free(a);
    } 

macro pSimpTest =
 #include<stdio.h>
    #include<stdlib.h>
    void main() {
     int x,y,z;
x = malloc(3) ;
y = malloc(4) ;
if (x == 0 && y == 1) z = 1 ;
else z = x + y ;
printf("%d;",z) ;
} 

syntax StmtList ::= split
macro split =
    p = *(a+b);
    l = b+1;
    r = e;
    while (l+1<= r) {
      if (*(a+l) <= p) {
        l = l + 1;
      } else { 
        r = r - 1;
        t=*(a+l);*(a+l)=*(a+r);*(a+r)=t;
      }
    }
    l = l - 1;
    t=*(a+l);*(a+l)=*(a+b);*(a+b)=t;

syntax Stmt ::= fNewArray  | fPrintArray
syntax Id ::= newArray | printArray
macro fNewArray = 
int newArray() {
  int n,a,p;
  scanf("%d",&n);
  p = a = malloc(n);
  while (p+1 <= a+n) {
    scanf("%d",p);
    p = p + 1;
  }
  return a;
}

macro fPrintArray = 
void printArray(a) {
  int e; e = a + sizeof(a) - 1;
  while (a <= e) { 
    printf("%d;",*a);
    a = a+1;
  }
}

syntax Pgm ::= pSeqQuickSort | pConcQuickSort
macro pSeqQuickSort = 
    #include<stdio.h>
    #include<stdlib.h>
void quickSort(a,b,e) {
  int p,l,r,t ;
  if (!(e <= b + 1)) {
    split
    quickSort(a,b,l); 
    quickSort(a,r,e);
  }
}
fNewArray
fPrintArray
void main() {
  int a;
  a = newArray();
  quickSort(a,0,sizeof(a));
  printArray(a);
  free(a);
}

macro pConcQuickSort = 
    #include<stdio.h>
    #include<stdlib.h>
void quickSort(a,b,e) {
  int p,l,r,t ;
  if (! (e <= b + 1)) {
    split
    spawn(quickSort(a,b,l)); 
    spawn(quickSort(a,r,e));
  }
}
fNewArray
fPrintArray
void main() {
  int a;
  a = newArray();
  quickSort(a,0,sizeof(a));
  printArray(a);
  free(a);
}


syntax Pgm ::= pRace1 | pRace2 | pRace3 
syntax Id ::= inc
macro pRace1 =
#include<stdio.h>
#include<stdlib.h>
void inc(a) {
  * a = * a + 1;
}
void main() {
  a = malloc(1);
  spawn(inc(a));
  spawn(inc(a));
}

macro pRace2 =
#include<stdio.h>
#include<stdlib.h>
void inc(a,b,t) {
  printf("%d;",t);
  * a = * a + 1;
  * b = * b + 1;
}
void main() {
  a = malloc(1);
  b = malloc(1);
  spawn(inc(a,b,1));
  spawn(inc(b,a,2));
}

syntax StmtList ::= cSynchronizedAccount | cDSynchronizedAccount | cGSynchronizedAccount 
                  | cSynchAcc ( StmtList ) | cBasicAccount
macro cBasicAccount =
int newAccount(m) {
  int a;
  a = malloc(1);
  *a = m;
  return a;
}

void deposit(a,m) {
  *a = *a+m;
}

void withdraw(a,m) {
  *a = *a-m;
}

void transfer(a,b,m) {
  *a = *a-m;
  *b = *b+m;
}

void print(a) {
  printf("%d;",*a);
}

syntax Id ::= newAccount | deposit | withdraw | transfer | m | run | run1 | run2

syntax Stmt ::= fTransfer | fDTransfer | fGTransfer

macro cSynchronizedAccount = cSynchAcc(fTransfer)
macro cDSynchronizedAccount = cSynchAcc(fDTransfer)
macro cGSynchronizedAccount = cSynchAcc(fGTransfer)

macro cSynchAcc(Sts) =
int newAccount(m) {
  int a;
  a = malloc(1);
  *a = m;
  return a;
}

void deposit(a,m) {
  acquire(a);
  *a = *a+m;
  release(a);
}

void withdraw(a,m) {
  acquire(a);
  *a = *a-m;
  release(a);
}

Sts

void print(a) {
  acquire(a);
  printf("%d;",*a);
  release(a);
}

macro fTransfer =
void transfer(a,b,m) {
  acquire(a);
  *a = *a-m;
  *b = *b+m;
  release(a);
}

macro fDTransfer = 
void transfer(a,b,m) {
  acquire(a);
  acquire(b);
  *a = *a-m;
  *b = *b+m;
  release(a);
  release(b);
}

macro fGTransfer = 
void transfer(a,b,m) {
  if (!(a <= b)) {
    acquire(a);
    acquire(b);
  } else {
    acquire(b);
    acquire(a);
  }
  *a = *a-m;
  *b = *b+m;
  release(a);
  release(b);
}

syntax Pgm ::= pAccount1 | pAccount2 | pAccount3 | pAccount4 | pAccount5
             | pAccountDriver1 ( StmtList ) | pAccountDriver2 ( StmtList )

macro pAccount1 = pAccountDriver1(cBasicAccount)
macro pAccount2 = pAccountDriver1(cSynchronizedAccount)
macro pAccountDriver1(Sts:StmtList) =
#include<stdio.h>
#include<stdlib.h>
Sts
void run(a,b) {
  deposit(a,300);
  withdraw(b,300);
}
void main() {
  int a,b;
  a = newAccount(100);
  b = newAccount(20);
  print(a);
  print(b);
  spawn(run(a,b));
  spawn(run(b,a));
  print(a);
  print(b);
}

macro pAccount3 = pAccountDriver2(cSynchronizedAccount)
macro pAccount4 = pAccountDriver2(cDSynchronizedAccount)
macro pAccount5 = pAccountDriver2(cGSynchronizedAccount)

macro  pAccountDriver2(Sts) =
#include<stdio.h>
#include<stdlib.h>
Sts
void run1(a,b) {
  deposit(a,300);
  withdraw(b,300);
  transfer(a,b,50);
}
void run2(a,b) {
  transfer(a,b,50);
  deposit(a,300);
  withdraw(b,300);
}
void main() {
  int a,b,c;
  a = newAccount(100);
  b = newAccount(20);
  print(a);
  print(b);
  spawn(run1(a,b));
  spawn(run2(b,a));
}

endkm

