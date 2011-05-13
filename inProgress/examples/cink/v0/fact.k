
load cink-compiled
load cink-syntax

kmod FACT is including CINK-SYNTAX
	syntax Id ::= <stdio.h> | fact | int | main | n | result 

	syntax Pgm ::= fact

	macro fact = 
#include <stdio.h>
 
     int fact(int n) {
           int result = 1;
           while (n > 0) {
             result = n * result; 
             n = n - 1;
           }
           return result;
         }
     int main() {
          int n;
          scanf("%d", &n);
          printf("%d;",fact(n));
     }
 


endkm
