    #include<stdio.h>
    #include<stdlib.h>
    #include<pAllocateLoop.c>
    #include<pPrint.c>
    #include<pFree.c>
    #include<pReverse.c>
    int main() {
      int * a = allocateLoop(7,NULL); print(a); a = reverse(a); print(a); free(a);
    } 


