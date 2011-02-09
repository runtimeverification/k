float static func(){
	return 5;
}

typedef float d_struct;
first(){
	extern d_struct func();
}
d_struct second(){
	d_struct n = func();
	return n;
}

int main(void){
	d_struct myn = second();
	int x = myn;
	return x;
}
