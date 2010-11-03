int main(void){
	struct { char a[2]; } x11 = {"h"};
	*(x11.a);
	return 0;
}
