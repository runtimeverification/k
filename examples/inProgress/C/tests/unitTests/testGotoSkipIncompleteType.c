
int test1(void){
	goto test1a;
	int x[] = {1, 2, 3}; // we skip over the init (although the memory is allocated)
	test1a:
	x[2] = 5;
	return 5 != x[2];
}


int main(void){
	if (test1()) { return 1; }
	
	return 0;
}
