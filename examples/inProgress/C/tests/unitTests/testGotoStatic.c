int f(int x){
	int retval = 0;
	if (x % 2 == 1){
		goto pastStatic;
	}
	static int staticInt;
	pastStatic:
	retval = ++staticInt;
	return retval;
}

int main(void){
	int retval = 0;
	for (int i = 0; i < 10; i++) {
		retval = f(i);
	}
	return retval;
}
