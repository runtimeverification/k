
load cink-compiled
load sym-int
load cink-syntax

kmod FOO2 is including CINK-SYNTAX
	syntax Id ::= f | i | main | n | x 

	syntax Pgm ::= foo2

	macro foo2 = 
    int f(int n) {
        int x;
        x = n;
        return x;
     }
     int main() {
        int i;
        int n;
        scanf("%d", &n);
        if (n > 0) {
           f(i);
        }
     }


endkm
