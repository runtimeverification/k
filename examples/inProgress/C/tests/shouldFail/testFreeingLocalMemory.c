// this program shouldn't run
int main(void){
	int* p;
	{
		int x = 5;
		p = &x;
	} // the memory for x should not be accessible now
	int y = *p;
	return y;
}
