load kernelc-syntax
kmod KERNELC-RECONFIG is including KERNELC-SYNTAX 
macro pReconfig =

#include <stdio.h>
#include <stdlib.h>

int nrand(int n) {
  return rand()%n;
}

int main() {
  int x = 1;
  while (x) {
    if (nrand(100)<5) {x=x+-1;} else {x=x+1;}
  }
  return 0;
}



syntax Pgm ::= pReconfig 
syntax #Id ::=  x | n | nrand  
endkm

