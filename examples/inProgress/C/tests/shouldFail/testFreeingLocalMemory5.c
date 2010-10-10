int* f(int z){
	{ 
		return &z;
	}
}
int main(void){
	int* p = f(5);
	int y = *p;
	return y;
}
