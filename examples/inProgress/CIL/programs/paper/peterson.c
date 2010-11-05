#include <stdio.h>
#include <stdlib.h>

void critical1() {
	//gSharedCounter++;
}
void critical2() {
	//gSharedCounter++;
}

void peterson1(char *flag, char *turn, register int t) {
	flag[t] = 1;
	*turn = 1 - t;
	while (flag[1 - t] && *turn == 1 - t) {}
	// printf("%d;", -1 - t);
	// printf("%d;", 1 + t);
	critical1();
	flag[t] = 0;
}

void peterson2(char *flag, char *turn, register int t) {
	flag[t] = 1;
	*turn = 1 - t;
	while (flag[1 - t] && *turn == 1 - t) {}
	// printf("%d;", -1 - t);
	// printf("%d;", 1 + t);
	critical2();
	flag[t] = 0;
}

int main() {
	//int* flag = (int*)malloc(2 * sizeof(int));
	char flag[2];
	flag[0] = 0; 
	flag[1] = 0 ;
	//int * turn =  (int*)malloc(1 * sizeof(int));
	char turn;
	//int t1 = 
	spawn(peterson1, &flag, &turn, 0);
	//int t2 = 
	spawn(peterson2, &flag, &turn, 1);
	// join(t1);
	// join(t2);
	sync();
	return 0;
}
