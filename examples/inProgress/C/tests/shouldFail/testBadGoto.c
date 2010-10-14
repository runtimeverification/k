// this shouldn't run

int test1(void){
	goto test1a;
	int x = 0; // we skip over the init (although the memory is allocated)
	test1a:
	return x;
}


int main(void){
	test1();
	
	return 0;
}
