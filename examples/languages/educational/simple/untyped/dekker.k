kmod DEKKER-ALGORITHM is including SIMPLE-UNTYPED-SYNTAX
macro pDekker =
	var flag1 = 0;
	var flag2 = 0;
	var turn = 1;
	// var gSharedCounter = 0;
	// var gLoopCount = 5;

	function critical1() {
		// gSharedCounter++;
		// return 0; // simple won't let me have an empty function body
	}
	function critical2() {
		// gSharedCounter++;
		// return 0;
	}

	function dekker1() {
		flag1 = 1;
		turn = 2;
		while((flag2 == 1) and (turn == 2)) do 0 ;
		// Critical section
		critical1();
		// Let the other task run
		flag1 = 0;
	}

	function dekker2() {
		flag2 = 1;
		turn = 1;
		while((flag1 == 1) and (turn == 1)) do 0 ;
		// critical section
		critical2();
		// leave critical section
		flag2 = 0;
	}

	// 
	// Tasks, as a level of indirection
	// 
	function task1() {
		// printf("Starting task1\n");
		// for i = 0 to gLoopCount do {
		while(true) do {
			dekker1();
		}
		
		// Wait for the threads to end
		rendezvous(0);
	}
	function task2() {
		// printf("Starting task2\n");
		// for i = 0 to gLoopCount do {
		while(true) do {
			dekker2();
		}
		
		// Wait for the threads to end
		rendezvous(0);
	}

	function main() {
		// int expected_sum = gLoopCount * 2;

		// Start the threads
		spawn(task1());
		spawn(task2());
		
		// printf("Computed %d\n", gSharedCounter);
		// return gSharedCounter;
		return 0;
	}

syntax Stmts ::= pDekker
syntax Id ::= task1 
syntax Id ::= task2 
syntax Id ::= dekker1 
syntax Id ::= dekker2 
syntax Id ::= flag1 
syntax Id ::= flag2 
syntax Id ::= critical1 
syntax Id ::= critical2 
syntax Id ::= turn 
syntax Id ::= gLoopCount 
syntax Id ::= i
	
endkm
