int main(void){
	for (int i = 0; i < 100; i++){
		struct {
			int a;
			int b[2];
			int c : 2;
			struct {int a;} d;
			union {int a; struct {int b;} b;} e;
			int (*f)(void);
		} s[] = {{1}, {2}};
	}
	debug();
	return 0;
}
