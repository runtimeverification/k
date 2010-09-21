/* Verify that flexible arrays can be initialized from STRING_CST
   constructors. */
#include <stdio.h>

int basicInit = 5;
char basicInit2 = 10;
int basicArr[] = {15, 20};
/* Baselines.  */
struct {
  char a1c;
  char *a1p;
} a1 = {
  '4',
  "62"
};

struct {
  char a2c;
  char a2p[2];
} a2 = {
  'v',
  "cq"
};

/* The tests.  */
// this is nonconforming
// struct {
  // char a3c;
  // char a3p[];
// } a3 = {
  // 'o',
  // "wx"
// };
struct sa3 {
  char a3c;
  char a3p[];
};
struct sa3b {
	struct sa3 sa3;
	char a3p[3];
} a3 = {
  {'o'},
  "wx"
};

struct {
  char a4c;
  char a4p[2];
} a4 = {
  '9',
  { 'e', 'b' }
};

struct {
  char a5c;
  struct inner_Struct {
	char a5_c2;
	char a5p[2];
  } insane;
} a5 = {
  '9',
  {
	'7',
	{ 'z', 'd' } 
  }
};

int main(void) {
	if (basicInit != 5)
		printf("FAIL");
	if (basicInit2 != 10)
		printf("FAIL");
	if (basicArr[0] != 15)
		printf("FAIL");
	if (basicArr[1] != 20)
		printf("FAIL");

  if (a1.a1c != '4')
    printf("FAIL");
  if (a1.a1p[0] != '6')
    printf("FAIL");
  if (a1.a1p[1] != '2')
    printf("FAIL");
  if (a1.a1p[2] != '\0')
    printf("FAIL");

  if (a2.a2c != 'v')
    printf("FAIL");
  if (a2.a2p[0] != 'c')
    printf("FAIL");
  if (a2.a2p[1] != 'q')
    printf("FAIL");

  if (a3.sa3.a3c != 'o')
    printf("FAIL");
  if (a3.a3p[0] != 'w')
    printf("FAIL");
  if (a3.a3p[1] != 'x')
    printf("FAIL");
	
  if (a4.a4c != '9')
    printf("FAIL");
  if (a4.a4p[0] != 'e')
    printf("FAIL");
  if (a4.a4p[1] != 'b')
    printf("FAIL");

  return 0;
}
