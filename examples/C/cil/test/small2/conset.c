typedef unsigned short	setword;
typedef setword *	setptr;
extern setptr	Conset[];
typedef struct { setword	S[6]; }	symset;

void checksymbol(symset ss) {}
void Member(unsigned int m, setptr sp) {}

int main()
{
  Member((unsigned)(7), Conset[0]);
  Member((unsigned)(8), Conset[1]);
  checksymbol(*((symset *)Conset[6]));
  checksymbol(*((symset *)Conset[7]));
  return 0;
}

static setword	Q0[] = {
	1,
	0x03FD
};
static setword	Q1[] = {
	1,
	0x004C
};
static setword	Q2[] = {
	1,
	0x0000
};
static setword	Q3[] = {
	2,
	0x000E,	0x5210
};
static setword	Q4[] = {
	2,
	0x000E,	0x1210
};
static setword	Q5[] = {
	1,
	0x0C00
};
static setword	Q6[] = {
	1,
	0x000C
};
static setword	Q7[] = {
	2,
	0x000E,	0x0210
};
static setword	Q8[] = {
	3,
	0x0000,	0x0000,	0x0060
};
static setword	Q9[] = {
	4,
	0x0002,	0x0000,	0x0064,	0x0800
};
static setword	Q10[] = {
	1,
	0x0C00
};
static setword	*Conset[] = {
	Q10,	Q9,	Q8,	Q7,	Q6,	Q5,
	Q4,	Q3,	Q2,	Q1,	Q0
};
