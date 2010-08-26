#include <stdio.h>

int authenticated = 0;
int error = 0;
int authenticate(void){
	authenticated = 1;
}

int use(void) {
	if (!authenticated) {
		puts("Use without authentication!");
		error = 1;
	}
}

int main(void) {
	spawn(authenticate);
	if (!authenticated) {
	}
	spawn(use);
	//int x = printf("0") + printf("1");
	//printf("\nx = %d\n", x);
	//if (!error) { puts("SUCCESS!") }
	return 0;
}
// int main(void) {
	// //printf("VOLATILE: ");
	// int x = printf("0") + printf("1");
	// //printf("\nx = %d\n", x);
	// return x;
// }

/*
mod MODEL-CHECK-TEST is
	--- subsort S < State .
	--- var S : S .
	op Start : -> State .
	op zeros : -> Prop .
	eq (Start) |= zeros  = false .
	op ones : -> Prop .
	eq (Start) |= ones  = true .
endm

red modelCheck(Start, [](zeros -> <> ones)) .
*/
