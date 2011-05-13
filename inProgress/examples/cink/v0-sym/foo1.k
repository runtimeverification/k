
load cink-compiled
load sym-int
load cink-syntax

kmod FOO1 is including CINK-SYNTAX
	syntax Id ::= <stdio.h> | f | i | int | main | n 

	syntax Pgm ::= foo1

	macro foo1 = 
#include <stdio.h>
     int f() {
        int n;
        n = -1;
        return n;
     }
 
     int main() {
        int i = 1;
        if (i > 0)
           while (i > 0) { i = i+1+f(); }
        else
           i = 0;
     }
 


endkm
