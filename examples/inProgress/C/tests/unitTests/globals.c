int a = 5;
int* b = &a;
int c;
int d;

int main(void){
	c = 5;
	d = *(&c);
	return a + *b + c + d;
}
