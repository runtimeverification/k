#include <stdio.h>

// ---------------
int global_param_1 = 5;
int f1(int global_param_1){
	return global_param_1;
}

int f2(int global_param_2){
	return global_param_2;
}
// ---------------
int global_local_1 = 5;
int g1(){
	int global_local_1 = 7;
	return global_local_1;
}

int g2(){
	int global_local_2 = 7;
	return global_local_2;
}
int global_local_2 = 5;
// ---------------
int main(void){
	int err = 0;
	// ---------------
	if (f1(7) != 7) {
		printf("failed global_param_1\n");
		err += 1;
	}
	if (f2(7) != 7) {
		printf("failed global_param_2\n");
		err += 1;
	}
	// ---------------
	if (g1() != 7) {
		printf("failed global_local_1\n");
		err += 1;
	}
	if (g2() != 7) {
		printf("failed global_local_2\n");
		err += 1;
	}
	// ---------------
	if (! err){
		printf("SUCCESS\n");
	}
	return 0;
}
