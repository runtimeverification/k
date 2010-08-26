/*
 * based on code by  J. Senning
 * 
 * 
 * A solution to the dining philosophers problem, using pthreads, semaphores
 * and shared memory.
 *
 * Written 02/22/1998 by J. Senning based on code provided by R. Bjork
 * Revised 01/04/2000 by J. Senning
 */

#include <stdio.h>
#include <stdlib.h>

//#define NUM_PHILOSOPHERS	3
#define MAX_PHILOSOPHERS 10
#define MEALS_PER_PHILOSOPHER 1

int NUM_PHILOSOPHERS;

/*--------------------------------------------------------------------------*/

// Each chopstick is represented by a lock.  We also need a lock to control modifications of the shared variables.
char chopstick[MAX_PHILOSOPHERS];
char mutex;

int total_number_of_meals = 0;

/*--------------------------------------------------------------------------*/
/*
 * To obtain his chopsticks, a philosopher does a semaphore wait on each.
 * Alternating order prevents deadlock.
 */
// void obtain_chopsticks( int n ) {
	// if ( n % 2 == 0 ) {
		// /* Even number: Left, then right */
		// lock(&chopstick[(n+1) % NUM_PHILOSOPHERS]);
		// lock(&chopstick[n]);
	// } else {
		// /* Odd number: Right, then left */
		// lock(&chopstick[n]);
		// lock(&chopstick[(n+1) % NUM_PHILOSOPHERS]);
	// }
// }

/*
 * To release his chopsticks, a philosopher does a semaphore signal on each.
 * Order does not matter.
 */
// void release_chopsticks( int n ) {
	// unlock(&chopstick[n]);
	// unlock(&chopstick[(n+1) % NUM_PHILOSOPHERS]);
// }

/*--------------------------------------------------------------------------*/

/*
 * Simulate a philosopher - endlessly cycling between eating and thinking
 * until his "life" is over.  Since this is called via pthread_create(), it
 * must accept a single argument which is a pointer to something.  In this
 * case the argument is a pointer to an array of two integers.  The first
 * is the philosopher number and the second is the duration (in seconds)
 * that the philosopher sits at the table.
 */
void philosopher( int n ) {
    //int eat_count = 0;
    //int n = philosopher_data;
    //int duration = philosopher_data[1];

	//while(eat_count < MEALS_PER_PHILOSOPHER) {
	while(1) {
		/* Hungry */
		
		//obtain_chopsticks( n );
		// obtain chopsticks
	    //if ( n % 2 == 0 ) {
			/* Even number: Left, then right */
			lock(&chopstick[(n+1) % NUM_PHILOSOPHERS]);
			lock(&chopstick[n]);
		// } else {
			// /* Odd number: Right, then left */
			// lock(&chopstick[n]);
			// lock(&chopstick[(n+1) % NUM_PHILOSOPHERS]);
		// }
		
		/* Eating */
		//eat_count++;
		//release_chopsticks( n );
		
		// release chopsticks
		unlock(&chopstick[n]);
		unlock(&chopstick[(n+1) % NUM_PHILOSOPHERS]);
		
		/* Think */
    }

    /* Update the shared variable database */

    // lock(&mutex);
    // total_number_of_meals += eat_count;
    // unlock(&mutex);
}

/*==========================================================================*/

int main( int argc, char *argv[] ) {
	NUM_PHILOSOPHERS = atoi(argv[1]);
	//printf("NUM_PHILOSOPHERS = %d\n", NUM_PHILOSOPHERS);
	//char philosopher_data[MAX_PHILOSOPHERS][1]; // might can be single variable if no other data

	// Create a thread for each philosopher.
	for (int i = 0; i < NUM_PHILOSOPHERS; i++ ) {
		//philosopher_data[i][0] = i;
		//philosopher_data[i][1] = duration;
		//spawn(philosopher, &philosopher_data[i]);
		spawn(philosopher, i);
	}

	// Wait for the philosophers to finish.
	sync();

	// Produce the final report.
	printf( "Total meals served = %d\n", total_number_of_meals );

	return 0;
}
