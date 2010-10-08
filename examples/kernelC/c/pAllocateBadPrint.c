    #include<stdio.h>
    #include<stdlib.h>
    #include<pAllocateLoop.c>
    #include<pPrint.c>
    #include<pFree.c>
    int main() {
      int * a = allocateLoop(2,(int *)malloc(2*sizeof(int))); print(a); free(a);
    } 

