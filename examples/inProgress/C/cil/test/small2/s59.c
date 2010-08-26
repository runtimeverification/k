typedef unsigned char	hashtyp;
typedef unsigned short	strindx;


typedef struct S59 *	idptr;
typedef struct S59 {
	idptr	inext;
	unsigned char	inref;
	hashtyp	ihash;
	strindx	istr;
}	idnode;

void printtok(strindx istr){}

 void
printid(ip)
	idptr	ip;
{
	printtok(ip->istr);
}

int main()
{
  return 0;
}
