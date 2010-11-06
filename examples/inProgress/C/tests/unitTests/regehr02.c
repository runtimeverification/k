int foo(void){
	signed char x = 1;
	unsigned char y = 255;
	return x > y;
}
int main(void){
	return foo();
}
