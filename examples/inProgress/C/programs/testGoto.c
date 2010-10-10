int test1(void){
	int x = 0;
	goto test1a;
	x = 5;
	test1a:
	return x;
}

int test2(void){
	int x = 0;
	goto test2a;
	{
		x = 5;
		int y;
		test2a:
		y = 0;
		return (y != x);
	}
	return 1;
}

int main(void){
	if (test1()) return 1;
	if (test2()) return 2;
	return 0;
}
