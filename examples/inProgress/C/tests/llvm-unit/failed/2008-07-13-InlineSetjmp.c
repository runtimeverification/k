// PR2486

#include <setjmp.h>      
#include <stdio.h>
jmp_buf g;
static int a() {longjmp(g,1);}
static void b(int* x) {if (setjmp(g))return;*x = 10;a();}
int main() {int a = 1; b(&a); printf("%d\n", a); return 0;}

