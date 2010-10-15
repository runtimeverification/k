#include <stdio.h>

void doSwitch(int n){
	switch (n) {
	  case 0:
	    printf("%d: You typed zero.\n", n);
	    break;
	  case 1:
	  case 9:
	    printf("%d: is a perfect square.\n", n);
	    break;  
	  case 2:
	    printf("%d: is an even number.\n", n);
	  case 3:
	  case 5:
	  case 7:
	    printf("%d: is a prime number.\n", n);
	    break;
	  case 4:
	    printf("%d: is a perfect square.\n", n);
	  case 6:
	  case 8:
	    printf("%d: is an even number.\n", n);
	    break;
	  default:
	    printf("%d: Only single-digit numbers are allowed.\n", n);
	    break;
	}
}

int myswitch(int count){
	unsigned x;
	printf ("The count is %d.  \nThis is ", count);
	switch (count) {
		case 0:
			printf ("none.\n");
			break;
		case 1:
			printf ("only one.\n");
			break;
		case 2:
			insideTwo:
			printf ("a pair.\n");
			break;
		case 3:
			printf ("three.\n");
			break;
		case 4:
			insideFour:
			printf ("four.\n");
			printf("inside switch, going to break\n");
			break;
		default:
			printf ("many.\n");
			break;
	}
	printf("Broke\n");
	next:

	return 0;
}

int main(void) {
	for (int i = 0; i < 11; i++){
		doSwitch(i);
	}
	for (int i = 0; i < 6; i++){
		myswitch(i);
	}
	return 0;
}
