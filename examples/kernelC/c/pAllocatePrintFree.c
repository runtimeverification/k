    #include<stdio.h>
    #include<stdlib.h>
    #include<pAllocateLoop.c>
    #include<pPrint.c>
    #include<pFree.c>
    int main() {
      int * a = allocateLoop(5,NULL); print(a); freeList(a);
    } 

