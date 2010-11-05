typedef unsigned short	setword;

typedef struct { setword	S[6]; }	symset;

typedef char	boolean;
boolean	Member(), Le(), Ge(), Eq(), Ne();

typedef enum { sand, sarray, sbegin, scase,
	sconst, sdiv, sdo, sdownto,
	selse, send, sextern, sfile,
	sfor, sforward, sfunc, sgoto,
	sif, sinn, slabel, smod,
	snil, snot, sof, sor,
	sother, spacked, sproc, spgm,
	srecord, srepeat, sset, sthen,
	sto, stype, suntil, svar,
	swhile, swith, seof, sinteger,
	sreal, sstring, schar, sid,
	splus, sminus, smul, squot,
	sarrow, slpar, srpar, slbrack,
	srbrack, seq, sne, slt,
	sle, sgt, sge, scomma,
	scolon, ssemic, sassign, sdotdot,
	sdot } 	symtyp;

typedef unsigned char	hashtyp;
typedef unsigned short	strindx;
	
typedef struct S59 *	idptr;
typedef struct S59 {
	idptr	inext;
	unsigned char	inref;
	hashtyp	ihash;
	strindx	istr;
}	idnode;


typedef struct S180 {
	symtyp	st;
	union {
		struct  {
			idptr	vid;
		} V1;
		struct  {
			char	vchr;
		} V2;
#if 0
        	struct  {
        		integer	vint;
        	} V3;
        	struct  {
        		strindx	vflt;
        	} V4;
        	struct  {
        		strindx	vstr;
        	} V5;
#endif // 0
	} U;
}	lexsym;

lexsym	currsym;

void error();

typedef enum { ebadsymbol, elongstring, elongtokn, erange,
	emanytokn, enotdeclid, emultdeclid, enotdecllab,
	emultdecllab, emuldeflab, ebadstring, enulchr,
	ebadchar, eeofcmnt, eeofstr, evarpar,
	enew, esetbase, esetsize, eoverflow,
	etree, etag, euprconf, easgnconf,
	ecmpconf, econfconf, evrntfile, evarfile,
	emanymachs, ebadmach } 	errors;

 void
checksymbol(ss)
	symset	ss;
{
	if (!(Member((unsigned)(currsym.st), ss.S)))
		error(ebadsymbol);
}

#if 0
static boolean
Member(m, sp)
        register unsigned int	m;
        register setptr	sp;
{
        register unsigned int	i = m / (setbits+1) + 1;

        if ((i <= *sp) && (sp[i] & (1 << (m % (setbits+1)))))
        	return (true);
        return (false);
}    
#else
static boolean Member() { return 1; }
#endif


int main()
{
  return 0;
}
