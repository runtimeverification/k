int f(void){
	register int i = 0;
	int retval = 0;
	for (int i = 0; i < 10; i++){
		retval += i;
	}
	return retval;
}

int main(void){
	int fx = f();
	return fx;
}
