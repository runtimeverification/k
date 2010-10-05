int f(int (*x)[], int num){
	int sum = 0;
	// printf("&x=%p\n", &x);
	// printf("x=%p\n", x);
	// printf("*x=%p\n", *x);
	// printf("**x=%d\n", **x);
	// printf("*((int (*)[])*x)=%p\n", *((int (*)[])*x));
	for (int i = 0; i < num; i++){
		sum += (*x)[i];
	}
	// int** p = (int**)&p;
	// printf("&p\t=\t\t%p\n", &p);
	// printf("p\t=\t\t%p\n", p);
	// printf("*p\t=\t\t%p\n", *p);
	// printf("**p\t=\t\t%p\n", *((int**)*p));
	//printf("*((int (*)[])*x) =\t%p\n", *((int (*)[])*x));
	return sum;
}

int main(void){
	int arr[3] = {1, 2, 3};
	// printf("&arr\t=\t\t%p\n", &arr);
	// printf("arr\t=\t\t%p\n", arr);
	int (*z)[] = &arr;
	if (f(z, 3) != 6){
		printf("Bug\n");
	}
	return 0;
}
