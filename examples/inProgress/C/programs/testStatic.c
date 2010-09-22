int x = 17;
int f(void){
	static int x;
	x++;
	{static int x; x = 12;}
	return x;
}

int g(void){
	static int x;
	x++;
	return x;
}

int main(void){
	int x = 5;
	f();f();
	g();g();g();
	return f() + g();
}
