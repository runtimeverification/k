/* xlisp - a small subset of lisp */
/*	Copyright (c) 1985, by David Michael Betz
	All Rights Reserved
	Permission is granted for unrestricted non-commercial use	*/

/* system specific definitions */
/* #define unix */

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <setjmp.h>

/* WES */
#include <string.h>

/* sm: let "make clean build" not choke on __HEAPIFY */
#ifndef __HEAPIFY
  #define __HEAPIFY
#endif

/* NNODES	number of nodes to allocate in each request (1000) */
/* TDEPTH	trace stack depth (500) */
/* EDEPTH	evaluation stack depth (1000) */
/* FORWARD	type of a forward declaration () */
/* LOCAL	type of a local function (static) */
/* AFMT		printf format for addresses ("%x") */
/* FIXNUM	data type for fixed point numbers (long) */
/* ITYPE	fixed point input conversion routine type (long atol()) */
/* ICNV		fixed point input conversion routine (atol) */
/* IFMT		printf format for fixed point numbers ("%ld") */
/* FLONUM	data type for floating point numbers (float) */
/* SYSTEM	enable the control-d command */

/* absolute value macros */
#ifndef abs
#define abs(n)	((n) < 0 ? -(n) : (n))
#endif
#ifndef fabs
#define fabs(n)	((n) < 0.0 ? -(n) : (n))
#endif


/* default important definitions */
#define NNODES		1000
#define TDEPTH		500
#define EDEPTH		1000

#ifndef FORWARD
#define FORWARD
#endif
#ifndef LOCAL
#define LOCAL		static
#endif
#ifndef AFMT
#define AFMT		"%x"
#endif
#ifndef FIXNUM
#define FIXNUM		long
#endif
#ifndef ITYPE
#define ITYPE		long atol()
#endif
#ifndef ICNV
#define ICNV(n)		atol(n)
#endif
#ifndef IFMT
#define IFMT		"%ld"
#endif
#ifndef FLONUM
#define FLONUM		float
#endif

/* useful definitions */
#define TRUE	1
#define FALSE	0
#ifndef NIL
#define NIL	(NODE *)0
#endif

/* program limits */
#define STRMAX		100		/* maximum length of a string constant */
#define HSIZE		199		/* symbol hash table size */
#define SAMPLE		100		/* control character sample rate */
	
/* node types */
#define FREE	0
#define SUBR	1
#define FSUBR	2
#define LIST	3
#define SYM	4
#define INT	5
#define STR	6
#define OBJ	7
#define FPTR	8
#define FLOAT	9
#define VECT	10

/* node flags */
#define MARK	1
#define LEFT	2

/* string types */
#define DYNAMIC	0
#define STATIC	1

/* new node access macros */
#define ntype(x)	((x)->n_type)

/* type predicates */
#define atom(x)		((x) == NIL || (x)->n_type != LIST)
#define null(x)		((x) == NIL)
#define listp(x)	((x) == NIL || (x)->n_type == LIST)
#define consp(x)	((x) && (x)->n_type == LIST)
#define subrp(x)	((x) && (x)->n_type == SUBR)
#define fsubrp(x)	((x) && (x)->n_type == FSUBR)
#define stringp(x)	((x) && (x)->n_type == STR)
#define symbolp(x)	((x) && (x)->n_type == SYM)
#define filep(x)	((x) && (x)->n_type == FPTR)
#define objectp(x)	((x) && (x)->n_type == OBJ)
#define fixp(x)		((x) && (x)->n_type == INT)
#define floatp(x)	((x) && (x)->n_type == FLOAT)
#define vectorp(x)	((x) && (x)->n_type == VECT)

/* cons access macros */
#define car(x)		((x)->n_car)
#define cdr(x)		((x)->n_cdr)
#define rplaca(x,y)	((x)->n_car = (y))
#define rplacd(x,y)	((x)->n_cdr = (y))

/* symbol access macros */
#define getvalue(x)	((x)->n_symvalue)
#define setvalue(x,v)	((x)->n_symvalue = (v))
#define getplist(x)	((x)->n_symplist->n_cdr)
#define setplist(x,v)	((x)->n_symplist->n_cdr = (v))
#define getpname(x)	((x)->n_symplist->n_car)

/* vector access macros */
#define getsize(x)	((x)->n_vsize)
#define getelement(x,i)	((x)->n_vdata[i])
#define setelement(x,i,v) ((x)->n_vdata[i] = (v))

/* object access macros */
#define getclass(x)	((x)->n_vdata[0])
#define getivar(x,i)	((x)->n_vdata[i+1])
#define setivar(x,i,v)	((x)->n_vdata[i+1] = (v))

/* subr/fsubr access macros */
#define getsubr(x)	((x)->n_subr)

/* fixnum/flonum access macros */
#define getfixnum(x)	((x)->n_int)
#define getflonum(x)	((x)->n_float)

/* string access macros */
#define getstring(x)	((x)->n_str)
#define setstring(x,v)	((x)->n_str = (v))

/* file access macros */
#define getfile(x)	((x)->n_fp)
#define setfile(x,v)	((x)->n_fp = (v))
#define getsavech(x)	((x)->n_savech)
#define setsavech(x,v)	((x)->n_savech = (v))

/* symbol node */
#define n_symplist	n_info.n_xsym.xsy_plist
#define n_symvalue	n_info.n_xsym.xsy_value

/* subr/fsubr node */
#define n_subr		n_info.n_xsubr.xsu_subr

/* list node */
#define n_car		n_info.n_xlist.xl_car
#define n_cdr		n_info.n_xlist.xl_cdr

/* integer node */
#define n_int		n_info.n_xint.xi_int

/* float node */
#define n_float		n_info.n_xfloat.xf_float

/* string node */
#define n_str		n_info.n_xstr.xst_str
#define n_strtype	n_info.n_xstr.xst_type

/* file pointer node */
#define n_fp		n_info.n_xfptr.xf_fp
#define n_savech	n_info.n_xfptr.xf_savech

/* vector/object node */
#define n_vsize		n_info.n_xvect.xv_size
#define n_vdata		n_info.n_xvect.xv_data

#ifdef CCURED_MODIFICATIONS
// modified definition that makes the union less scary
/* node structure */
typedef struct node {
  char n_type;		/* type of node */
  char n_flags;		/* flag bits */

  struct {

    union { 
      struct xsym {		/* symbol node */
        struct node *xsy_plist;	/* symbol plist - (name . plist) */
        struct node *xsy_value;	/* the current value */
      } n_xsym;
      struct xlist {		/* list node (cons) */
        struct node *xl_car;	/* the car pointer */
        struct node *xl_cdr;	/* the cdr pointer */
      } n_xlist;
    } ; // transparent

      struct xsubr {		/* subr/fsubr node */
        struct node *(*xsu_subr)(struct node *);	
      } n_xsubr;

      struct xint {		/* integer node */
        FIXNUM xi_int;		/* integer value */
      } n_xint;
      struct xfloat {		/* float node */
        FLONUM xf_float;		/* float value */
      } n_xfloat;

      struct xstr {		/* string node */
        int xst_type;		/* string type */
        char *xst_str;		/* string pointer */
      } n_xstr;

      struct xfptr {		/* file pointer node */
        FILE *xf_fp;		/* the file pointer */
        int xf_savech;		/* lookahead character for input files */
      } n_xfptr;

      struct xvect {		/* vector node */
        int xv_size;		/* vector size */
        struct node **xv_data;	/* vector data */
      } n_xvect;

  } n_info ; 
} NODE;
#else
// original definition
typedef struct node {
    char n_type;		/* type of node */
    char n_flags;		/* flag bits */
    union {			/* value */
	struct xsym {		/* symbol node */
	    struct node *xsy_plist;	/* symbol plist - (name . plist) */
	    struct node *xsy_value;	/* the current value */
	} n_xsym;
	struct xsubr {		/* subr/fsubr node */
            /* WEIMER struct node *(*xsu_subr)();	pointer to an internal routine */
            struct node *(*xsu_subr)(struct node *);	
	} n_xsubr;
	struct xlist {		/* list node (cons) */
	    struct node *xl_car;	/* the car pointer */
	    struct node *xl_cdr;	/* the cdr pointer */
	} n_xlist;
	struct xint {		/* integer node */
	    FIXNUM xi_int;		/* integer value */
	} n_xint;
	struct xfloat {		/* float node */
	    FLONUM xf_float;		/* float value */
	} n_xfloat;
	struct xstr {		/* string node */
	    int xst_type;		/* string type */
	    char *xst_str;		/* string pointer */
	} n_xstr;
	struct xfptr {		/* file pointer node */
	    FILE *xf_fp;		/* the file pointer */
	    int xf_savech;		/* lookahead character for input files */
	} n_xfptr;
	struct xvect {		/* vector node */
	    int xv_size;		/* vector size */
	    struct node **xv_data;	/* vector data */
	} n_xvect;
    } n_info ; 
} NODE;
#endif

/* execution context flags */
#define CF_GO		1
#define CF_RETURN	2
#define CF_THROW	4
#define CF_ERROR	8
#define CF_CLEANUP	16
#define CF_CONTINUE	32
#define CF_TOPLEVEL	64

/* execution context */
typedef struct context {
    int c_flags;			/* context type flags */
    struct node *c_expr;		/* expression (type dependant) */
    jmp_buf c_jmpbuf;			/* longjmp context */
    struct context *c_xlcontext;	/* old value of xlcontext */
    struct node ***c_xlstack;		/* old value of xlstack */
    struct node *c_xlenv;		/* old value of xlenv */
    int c_xltrace;			/* old value of xltrace */
} CONTEXT;

/* function table entry structure */
struct fdef {
    char *f_name;			/* function name */
    int f_type;				/* function type SUBR/FSUBR */
    //sm: struct node *(*f_fcn)();		/* function code */
    struct node *(*f_fcn)(NODE*);		/* function code */
};

/* memory segment structure definition */
struct segment {
    int sg_size;
    struct segment *sg_next;
    // sm: changing this to be an open array
    //struct node sg_nodes[1];
    struct node sg_nodes[0];
};


