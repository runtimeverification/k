/*
 * Dekker's algorithm
 */
// based on code found at http://jakob.engbloms.se/archives/65
// original file written by Jakob Engblom

#include <stdio.h>
#include <stdlib.h>

static volatile int flag1 = 0;
static volatile int flag2 = 0;
static volatile int turn  = 1;
//static volatile int gSharedCounter = 0;
//int gLoopCount = 5;

void critical1() {
	//gSharedCounter++;
}
void critical2() {
	//gSharedCounter++;
}

void dekker1(void) {
	flag1 = 1;
	turn = 2;
	while((flag2 == 1) && (turn == 2)) ;
	// Critical section
	critical1();
	// Let the other task run
	flag1 = 0;
}

void dekker2(void) {
	flag2 = 1;
	turn = 1;
	while((flag1 == 1) && (turn == 1)) ;
	// critical section
	critical2();
	// leave critical section
	flag2 = 0;
}

//
// Tasks, as a level of indirection
//
void task1(void) {
	// printf("Starting task1\n");
	// for (int i = 0; i < gLoopCount; i++) {
	while(1) {
		dekker1();
	}
}

void task2(void) {
	// printf("Starting task2\n");
	// for (int i = 0; i < gLoopCount; i++) {
	while(1) {
		dekker2();
	}
}

int main(void) {
	//int expected_sum = gLoopCount * 2;

	/* Start the threads */
	spawn(task1);
	spawn(task2);

	/* Wait for the threads to end */
	sync();
	
	//printf("Computed %d\n", gSharedCounter);
	//return gSharedCounter;
	return 0;
}

/*
--- START MODEL-CHECKING
--- mod MODEL-CHECKER
--- including C-program-dekker .
	including PL-MODEL-CHECKER .
	op state : Bag -> Model-Checker-State .
	op Start : -> Model-Checker-State .
	---eq Start = state(eval('program-dekker)) .
	op enabled : Id -> Prop .
	eq
		state(? < T >... < k > 'Apply('Closure(X:Id,, ?,, ?),, ?) ...</ k > ...</ T >) |= enabled(X:Id) = true .
--- endm
--- END MODEL-CHECKING

erew modelCheck(Start, <> enabled) .

*/
