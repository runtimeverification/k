int main(void){
	volatile int x = 0;
	x = x + 1;
	const int y = 2;
	const int * restrict z = &y;
	int w = 3;
	int * restrict r = &w;
	
	return x + y + *z + *r;
}
