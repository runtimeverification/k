
load cink-compiled
load sym-int
load cink-syntax

kmod FOO3 is including CINK-SYNTAX
	syntax Id ::= f | i | main | n | x 

	syntax Pgm ::= foo3

	macro foo3 = 
    int f(int n) {
        int x;
        x = n;
        unlock();
        return x + 1;
     }
     int main() {
        int i;
        int n;
        lock();
        scanf("%d", &n);
        if (n > 0) {
           f(n);
        }
        unlock();
     }


endkm
