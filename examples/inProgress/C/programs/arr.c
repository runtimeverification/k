#include <stdio.h>
struct point {
	int x;
	int y;
};

#define OK { printf("OK\n"); }

typedef int* intp;
int main(void){
	int arr[2][2] = {{1, 2}, {3, 4}};
	int typetest = sizeof(arr) * 2;
	intp myintp = (intp)& arr;
	myintp = & typetest;
	//unsigned char bob[] = "hello bob";
	char* bob = "hello";
	// printf("sizeof(bob)=%d\n", sizeof(bob));
	// printf("sizeof(\"hello\")=%d\n", sizeof("hello"));
	
	// for(int i = 0; i < 2; i++){
		// for(int j = 0; j < 2; j++){
			// printf("VOLATILE %d\n", &arr[i][j]);
		// }
	// }
	
	
	if ((int*)(&arr) != (int*)(arr)) {
		printf("&arr != arr\n");
	} else OK
	if ((int*)(&arr[0]) != (int*)(arr)) {
		printf("&arr[0] != arr\n");
	} else OK
	if ((int*)(&*(arr + 0)) != (int*)(arr)) {
		printf("&*(arr + 0) != arr\n");
	} else OK
	if ((int*)((arr + 0)) != (int*)(arr)) {
		printf("arr + 0 != arr\n");
	} else OK
	if ((int*)(&(*(*(arr + 0) + 0))) != (int*)(arr)) {
		printf("&(*(*(arr + 0) + 0)) != arr\n");
	} else OK
	
	if (*((int*)arr + 0) != 1){
		printf("*((int*)arr + 0) != 1\n");
	} else OK
	if (*((int*)arr + 1) != 2){
		printf("*((int*)arr + 1) != 2\n");
	} else OK
	if (*((int*)arr + 2) != 3){
		printf("*((int*)arr + 2) != 3\n");
	} else OK
	if (*((int*)arr + 3) != 4){
		printf("*((int*)arr + 3) != 4\n");
	} else OK
	
	// if (
	// Lval(Mem(PlusPI(CastE(TPtr(TInt(int, ), ), StartOf(Var(arr, NoOffset))), Const(Int64(2,int,None))), NoOffset)) 
	// != Const(Int64(3,int,None))) {
	// Lval(Var(printf, NoOffset))(Const(CStr("*((int*)arr + 2) != 3\n")));
	// } else {
	// Lval(Var(printf, NoOffset))(Const(CStr("OK\n")));
	// }
	
	if (*((*(arr + 0)) + 0) != 1){
		printf("*((*(arr + 0)) + 0) != 1\n");
	} else OK
	if (*((*(arr + 0)) + 1) != 2){
		printf("*((*(arr + 0)) + 1) != 2\n");
	} else OK
	if (*((*(arr + 1)) + 0) != 3){
		printf("*((*(arr + 1)) + 0) != 3\n");
	} else OK
	if (*((*(arr + 1)) + 1) != 4){
		printf("*((*(arr + 1)) + 1) != 4\n");
	} else OK
	
	if ((int*)&arr[0] != (int*)&arr[0][0]){
		printf("&arr[0] != &arr[0][0]\n");
	} else OK
	if ((int*)&arr[1] != (int*)&arr[1][0]){
		printf("&arr[1] != &arr[1][0]\n");
	} else OK
	
	struct point pointArr[4];
	pointArr[0].x = 1;
	pointArr[0].y = 2;
	pointArr[1].x = 3;
	pointArr[1].y = 4;
	pointArr[2].x = 5;
	pointArr[2].y = 6;
	pointArr[3].x = 7;
	pointArr[3].y = 8;
	//int pointArrPlus3 = (int)(*(pointArr + 3)) ;
	//debug(0);
	if ((*(pointArr + 3)).x != 7) {
		printf("(*(pointArr + 3)).x != 7, == %d\n", (*(pointArr + 3)).x);
		//printf("(*(pointArr + 3)).x == %d\n", (*(pointArr + 3)).x);
	} else OK
	if ((*(pointArr + 3)).y != 8) {
		printf("(*(pointArr + 3)).y != 8, == %d\n", (*(pointArr + 3)).y);
		//printf("(*(pointArr + 3)).y == %d\n", (*(pointArr + 3)).y);
	} else OK
	if (*((int*)(&(*(pointArr + 3)))) != 7) {
		printf("*((int*)(&(*(pointArr + 3)))) != 7\n");
	} else OK
	if (*((int*)(&(*(pointArr + 3))) + 1) != 8) {
		printf("*((int*)(&(*(pointArr + 3))) + 1) != 8\n");
	} else OK
	
	//int anint = (int)(pointArr[0]);
	
	// The important issue is how the expression i > us is evaluated. Under the unsigned preserving rules (and under the value preserving rules on a machine where short integers and plain integers are the same size), us is promoted to unsigned int. The usual integral conversions say that when types unsigned int and int meet across a binary operator, both operands are converted to unsigned, so i is converted to unsigned int, as well. The old value of i, -5, is converted to some large unsigned value (65,531 on a 16-bit machine). This converted value is greater than 10, so the code prints ``whoops!'' 
	// unsigned short us = 10;
	// int i = -5;
	// if(i > us)
		// printf("whoops!\n");
		
	// unsigned char uc = 0x80;
	// unsigned long ul = 0;
	// ul |= uc << 8;
	// printf("0x%lx\n", ul);

// Before being left-shifted, uc is promoted. Under the unsigned preserving rules, it is promoted to an unsigned int, and the code goes on to print 0x8000, as expected. Under the value preserving rules, however, uc is promoted to a signed int (as long as int's are larger than char's, which is usually the case). The intermediate result uc << 8 goes on to meet ul, which is unsigned long. The signed, intermediate result must therefore be promoted as well, and if int is smaller than long, the intermediate result is sign-extended, becoming 0xffff8000 on a machine with 32-bit longs. On such a machine, the code prints 0xffff8000, which is probably not what was expected. (On machines where int and long are the same size, the code prints 0x8000 under either set of rules.) 

	
	// int x1 = 5;
	// unsigned int x2 = 5;
	// signed int x3 = 5;

	// int y1 = -5;
	// unsigned int y2 = -5;
	// signed int y3 = -5;
	
	// char z1 = 5;
	// unsigned char z2 = 5;
	// signed char z3 = 5;
	
	// int* ugg = (int*)15;
	// printf("ugg+2=%d\n", ugg + 2);
	
	// x1 = z1;
	// x1 = z2;
	// x1 = z3;
	// x2 = z1;
	// x2 = z2;
	// x2 = z3;
	// x3 = z1;
	// x3 = z2;
	// x3 = z3;
	
	// int x = 5;
	// //int dynArr[x];
	// //dynArr[0] = 25;
	// //int q = sizeof(dynArr);
	// int zeroArr[0];
	// // if arr[0][0] == *(arr + 0)
	// // if arr[0][1] == *(arr + 1)
	// // if arr[1][0] == *(arr + 2)
	// // if arr[1][1] == *(arr + 3)
	// printf("zeroArr=%d\n", zeroArr);
	// printf("&zeroArr=%d\n", &zeroArr);
	// printf("arr=%d\n", arr);
	// printf("&arr=%d\n", &arr);
	// printf("&arr[0]=%d\n", &arr[0]);
	// printf("&*(arr + 0)=%d\n", &*(arr + 0));
	// printf("(arr + 0)=%d\n", (arr + 0));
	// printf("&(*(*(arr + 0) + 0))=%d\n", &(*(*(arr + 0) + 0)));
	// printf("&arr[1]=%d\n", &arr[1]);
	// printf("&arr[0][0]=%d\n", &arr[0][0]);
	// printf("&arr[0][1]=%d\n", &arr[0][1]);
	// printf("&arr[1][0]=%d\n", &arr[1][0]);
	// printf("&arr[1][1]=%d\n", &arr[1][1]);
	// printf("arr[0][0]=%d\n", arr[0][0]);
	// printf("arr[0][1]=%d\n", arr[0][1]);
	// printf("arr[1][0]=%d\n", arr[1][0]);
	// printf("arr[1][1]=%d\n", arr[1][1]);
	// printf("sizeof(arr)=%d\n", sizeof(arr)/sizeof(int));
	// printf("sizeof(arr[0])=%d\n", sizeof(arr[0])/sizeof(int));
	// printf("sizeof(int[2][2])=%d\n", sizeof(int[2][2])/sizeof(int));
	//bob(5);
	return 0;
}
// struct bob bob(int x){
	// struct bob z;
	// return z;
// }
