int f(void){
	int went = 0;
	goto label1;
	static int z;
	label1:
	z++;
	label2: ;
	static int y;
	y++;
	if (!went) {
		went = 1;
		goto label2;
	}
	return z + y;
}

int main(void){
	f();
	f();
	f();
	return f();
}
