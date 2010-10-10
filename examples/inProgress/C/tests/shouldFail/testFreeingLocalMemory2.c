// this program shouldn't run

int* f(void){
	int x = 5;
	return &x;
}
int main(void){
	int* p = f();
	int y = *p;
	return y;
}
