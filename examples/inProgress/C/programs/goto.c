#include <stdio.h>

int gotowhile(void){
	int flag;
	flag = 1;
	
	if (flag) {
		goto target;
	}
	
	while (0){
		int local = 1;
		printf("local=%d\n", local);
	target:
		local = 0;
		printf("local=%d\n", local);
	}
	return 0;
}

int gotoloop(void){
	int n=10;
loop:
	printf("%d, ", n);
	n--;
	if (n>0) { 
		goto loop;
	}
	puts("Done!");
	return 0;
}

int sneaky(void){
	int loopGuard = 0;
	while (loopGuard == 0){
		goto sneaky;
		
		if (loopGuard != 0){
	sneaky:
			puts("sneaky");
			loopGuard = 1;
		} else {
			loopGuard = 0;
		}
	}
	return 0;
}

int last(void){
	int last = 0;
	int x = 5;
start:
	while (last < 5){
		last++;
		printf("%d, ", last);
		goto last;
	}
	goto end;
	last:
		goto start;
	end:
	return 0;
}

int another(void){
	int another = 5;
	goto insideLoop;
	another = 60;
	while (another > 0){
	insideLoop:
		printf("%d, ", another);
		another--;
	}
	puts("");
	goto repeatedLabel;
	repeatedLabel:
	return 0;
}

int myswitch(void){
	unsigned count;

	int thrice = 0;
	count = 2;
	printf ("The count is %d.  \nThis is ", count);
	//debug();
	switch (count) {
		case 0:
			printf ("none.\n");
			goto next;
		case 1:
			printf ("only one.\n");
			goto next;
		case 2:
			insideTwo:
			printf ("a pair.\n");
			goto next;
		case 3:
			printf ("three.\n");
			goto next;
		case 4:
			insideFour:
			printf("inside switch, going to break\n");
			break;
		case 5:
			insideFive:
			printf("inside switch, going to goto another case\n");
			goto insideTwo;
		default:
			printf ("many.\n");
			goto next;
	}
	printf("Broke\n");
	next:

	if (thrice == 0){
		printf("jumping into case\n");
		thrice = 1;
		goto insideTwo;
	} else if (thrice == 1){
		printf("jumping into weird case 1\n");
		thrice = 2;
		goto insideFour;
	} else if (thrice == 2){
		printf("jumping into weird case 2\n");
		thrice = 3;
		goto insideFive;
	}
	
	unsigned x = 4;
	printf ("The test number is %d.\n", x);
	while (x < 10) {
		++x;
		if (x % 2 == 0) {
			goto done;
		}
		printf ("%d is an odd number.\n", x);
	}
	done:
	goto repeatedLabel;
	return 0;
	repeatedLabel:
	return 1;
}

	
int main(void){
	printf("gotowhile: %d\n", gotowhile());
	printf("gotoloop: %d\n", gotoloop());	
	printf("sneaky: %d\n", sneaky());
	printf("myswitch: %d\n", myswitch());	
	printf("another: %d\n", another());	
	printf("last: %d\n", last());		
	
	return 0;
}
