#include <stdio.h>
#include <stdlib.h>

struct tmp
{
  long long int pad : 12;
  long long int field : 52;
};

struct tmp2
{
  long long int field : 52;
  long long int pad : 12;
};

struct tmp3
{
  long long int pad : 11;
  long long int field : 53;
};

struct tmp4
{
  long long int field : 53;
  long long int pad : 11;
};

struct tmp
sub (struct tmp tmp)
{
  tmp.field ^= 0x0008765412345678LL;
  return tmp;
}

struct tmp2
sub2 (struct tmp2 tmp2)
{
  tmp2.field ^= 0x0008765412345678LL;
  return tmp2;
}

struct tmp3
sub3 (struct tmp3 tmp3)
{
  tmp3.field ^= 0x0018765412345678LL;
  return tmp3;
}

struct tmp4
sub4 (struct tmp4 tmp4)
{
  tmp4.field ^= 0x0018765412345678LL;
  return tmp4;
}

struct tmp tmp = {0x123, 0x123456789ABCDLL};
struct tmp2 tmp2 = {0x123456789ABCDLL, 0x123};
struct tmp3 tmp3 = {0x123, 0x1FFFF00000000LL};
struct tmp4 tmp4 = {0x1FFFF00000000LL, 0x123};

int main(void) {

	if (sizeof (long long) != 8) {
		return 0;
	}

	tmp = sub (tmp);
	tmp2 = sub2 (tmp2);

	if (tmp.pad != 0x123 ){
		printf("tmp.pad != 0x123\n");
	}
	if (tmp.field != 0xFFF9551175BDFDB5LL) {
		printf("tmp.field != 0xFFF9551175BDFDB5LL, == %x\n", tmp.field);
	}	
	if (tmp2.pad != 0x123){
		printf("tmp2.pad != 0x123\n");
	}
	if (tmp2.field != 0xFFF9551175BDFDB5LL) {
		printf("tmp2.field != 0xFFF9551175BDFDB5LL, == %x\n", tmp2.field);
	}

	tmp3 = sub3 (tmp3);
	tmp4 = sub4 (tmp4);

	if (tmp3.pad != 0x123){
		printf("tmp3.pad != 0x123\n");
	}
	if (tmp3.field != 0xFFF989AB12345678LL) {
		printf("tmp3.field != 0xFFF989AB12345678LL, == %x\n", tmp3.field);
	}

	if (tmp4.pad != 0x123){
		printf("tmp4.pad != 0x123\n");
	}
	if (tmp4.field != 0xFFF989AB12345678LL) {
		printf("tmp4.field != 0xFFF989AB12345678LL, == %x\n", tmp4.field);
	}
	return 0;
}
