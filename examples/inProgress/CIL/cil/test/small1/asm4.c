// #define __INCLUDE_ALL
#ifdef __INCLUDE_ALL
#else

typedef signed char gint8;
typedef unsigned char guint8;
typedef signed short gint16;
typedef unsigned short guint16;
typedef signed int gint32;
typedef unsigned int guint32;

__extension__  typedef signed long long gint64;
__extension__  typedef unsigned long long guint64;

typedef char   gchar;

// sm: I think the intent here was just to use printf in an ordinary way,
// not test macros; egcs doens't like this one
//#define g_log(domain, level, format, ...) printf(format, __VA_ARGS__)

// it prefers no comma, and no __VA_ARGS__
#define g_log(domain, level, format, args...) printf(format, ## args)

#endif

int
main (int   argc,
      char *argv[])
{
  guint16 gu16t1 = 0x44afU, gu16t2 = 0xaf44U;
  guint32 gu32t1 = 0x02a7f109U, gu32t2 = 0x09f1a702U;

  guint64 gu64t1 = (__extension__  ( 0x1d636b02300a7aa7ULL)) ,
	  gu64t2 = (__extension__  ( 0xa77a0a30026b631dULL)) ;


   
  (void)( {	if (!( sizeof (gint8) == 1 ))	g_log (((gchar*) 0) ,	G_LOG_LEVEL_ERROR,	"file %s: line %d (%s): assertion failed: (%s)",	"type-test.c",	47,	__PRETTY_FUNCTION__,	"sizeof (gint8) == 1");			})  ;
  (void)( {	if (!( sizeof (gint16) == 2 ))	g_log (((gchar*) 0) ,	G_LOG_LEVEL_ERROR,	"file %s: line %d (%s): assertion failed: (%s)",	"type-test.c",	48,	__PRETTY_FUNCTION__,	"sizeof (gint16) == 2");			})  ;
  (void)( {	if (!( sizeof (gint32) == 4 ))	g_log (((gchar*) 0) ,	G_LOG_LEVEL_ERROR,	"file %s: line %d (%s): assertion failed: (%s)",	"type-test.c",	49,	__PRETTY_FUNCTION__,	"sizeof (gint32) == 4");			})  ;

  (void)( {	if (!( sizeof (gint64) == 8 ))	g_log (((gchar*) 0) ,	G_LOG_LEVEL_ERROR,	"file %s: line %d (%s): assertion failed: (%s)",	"type-test.c",	51,	__PRETTY_FUNCTION__,	"sizeof (gint64) == 8");			})  ;


  (void)( {	if (!( ((__extension__	({ register guint16 __v;	if (__builtin_constant_p (  gu16t1  ))	__v = ((guint16) ( (((guint16) (   gu16t1   ) & (guint16) 0x00ffU) << 8) | (((guint16) (   gu16t1   ) & (guint16) 0xff00U) >> 8))) ;	else	__asm__ __const__ ("rorw $8, %w0"	: "=r" (__v)	: "0" ((guint16) (  gu16t1  )));	__v; })) )  == gu16t2 ))	g_log (((gchar*) 0) ,	G_LOG_LEVEL_ERROR,	"file %s: line %d (%s): assertion failed: (%s)",	"type-test.c",	54,	__PRETTY_FUNCTION__,	"GUINT16_SWAP_LE_BE (gu16t1) == gu16t2");			})  ;
  (void)( {	if (!( ((__extension__	({ register guint32 __v;	if (__builtin_constant_p (  gu32t1  ))	__v = ((guint32) ( (((guint32) (   gu32t1   ) & (guint32) 0x000000ffU) << 24) | (((guint32) (   gu32t1   ) & (guint32) 0x0000ff00U) <<  8) | (((guint32) (   gu32t1   ) & (guint32) 0x00ff0000U) >>  8) | (((guint32) (   gu32t1   ) & (guint32) 0xff000000U) >> 24))) ;	else	__asm__ __const__ ("rorw $8, %w0\n\t"	"rorl $16, %0\n\t"	"rorw $8, %w0"	: "=r" (__v)	: "0" ((guint32) (  gu32t1  )));	__v; })) )  == gu32t2 ))	g_log (((gchar*) 0) ,	G_LOG_LEVEL_ERROR,	"file %s: line %d (%s): assertion failed: (%s)",	"type-test.c",	55,	__PRETTY_FUNCTION__,	"GUINT32_SWAP_LE_BE (gu32t1) == gu32t2");			})  ;

  (void)( {	if (!( ((__extension__	({ union { guint64 __ll;	guint32 __l[2]; } __r;	if (__builtin_constant_p (  gu64t1  ))	__r.__ll = ((guint64) ( (((guint64) (   gu64t1   ) &	(guint64) (__extension__  ( 0x00000000000000ffULL)) ) << 56) |	(((guint64) (   gu64t1   ) &	(guint64) (__extension__  ( 0x000000000000ff00ULL)) ) << 40) |	(((guint64) (   gu64t1   ) &	(guint64) (__extension__  ( 0x0000000000ff0000ULL)) ) << 24) |	(((guint64) (   gu64t1   ) &	(guint64) (__extension__  ( 0x00000000ff000000ULL)) ) <<  8) |	(((guint64) (   gu64t1   ) &	(guint64) (__extension__  ( 0x000000ff00000000ULL)) ) >>  8) |	(((guint64) (   gu64t1   ) &	(guint64) (__extension__  ( 0x0000ff0000000000ULL)) ) >> 24) |	(((guint64) (   gu64t1   ) &	(guint64) (__extension__  ( 0x00ff000000000000ULL)) ) >> 40) |	(((guint64) (   gu64t1   ) &	(guint64) (__extension__  ( 0xff00000000000000ULL)) ) >> 56))) ;	else	{	union { guint64 __ll;	guint32 __l[2]; } __w;	__w.__ll = ((guint64)   gu64t1  );	__r.__l[0] = ((__extension__	({ register guint32 __v;	if (__builtin_constant_p (  __w.__l[1]  ))	__v = ((guint32) ( (((guint32) (   __w.__l[1]   ) & (guint32) 0x000000ffU) << 24) | (((guint32) (   __w.__l[1]   ) & (guint32) 0x0000ff00U) <<  8) | (((guint32) (   __w.__l[1]   ) & (guint32) 0x00ff0000U) >>  8) | (((guint32) (   __w.__l[1]   ) & (guint32) 0xff000000U) >> 24))) ;	else	__asm__ __const__ ("rorw $8, %w0\n\t"	"rorl $16, %0\n\t"	"rorw $8, %w0"	: "=r" (__v)	: "0" ((guint32) (  __w.__l[1]  )));	__v; })) ) ;	__r.__l[1] = ((__extension__	({ register guint32 __v;	if (__builtin_constant_p (  __w.__l[0]  ))	__v = ((guint32) ( (((guint32) (   __w.__l[0]   ) & (guint32) 0x000000ffU) << 24) | (((guint32) (   __w.__l[0]   ) & (guint32) 0x0000ff00U) <<  8) | (((guint32) (   __w.__l[0]   ) & (guint32) 0x00ff0000U) >>  8) | (((guint32) (   __w.__l[0]   ) & (guint32) 0xff000000U) >> 24))) ;	else	__asm__ __const__ ("rorw $8, %w0\n\t"	"rorl $16, %0\n\t"	"rorw $8, %w0"	: "=r" (__v)	: "0" ((guint32) (  __w.__l[0]  )));	__v; })) ) ;	}	__r.__ll; })) )  == gu64t2 ))	g_log (((gchar*) 0) ,	G_LOG_LEVEL_ERROR,	"file %s: line %d (%s): assertion failed: (%s)",	"type-test.c",	57,	__PRETTY_FUNCTION__,	"GUINT64_SWAP_LE_BE (gu64t1) == gu64t2");			})  ;

  return 0;
}


