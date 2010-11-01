#include <stdio.h>

void hanoi(char,char,char,int);
int step = 0;
int main(void) {
    char t1='A',t2='B',t3='C';
    int n = 4;
    hanoi(t1,t2,t3,n);
	return 0;
}

void hanoi(char t1,char t2,char t3,int n) {
    step++;
    //printf("\n %c %c %c %d",t1,t2,t3,n);
    if(n==1) {
        //printf("\n%c ----> %c",t1,t2);
        return;
    }
    hanoi(t1,t3,t2,n-1);
    //printf("\n %c %c %c %d",t1,t2,t3,n);
    //printf("\n%c ----> %c",t1,t2);
   // printf("\n %c %c %c %d",t1,t2,t3,n);
    hanoi(t3,t2,t1,n-1);
    //printf("\n %c %c %c %d steps=%d",t1,t2,t3,n,step);
}
