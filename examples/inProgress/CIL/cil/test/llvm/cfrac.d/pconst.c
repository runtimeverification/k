#include "pdefs.h"

static precisionType pzeroConst = {
   (short) 1,		/* refcount (read/write!) */
   (posit) 1,		/* size */
   (posit) 1,		/* digitcount */
   (boolean) 0,		/* sign */
   { (digit) 0 }	/* value */
};

static precisionType poneConst = {
   (short) 1,		/* refcount (read/write!) */
   (posit) 1,		/* size */
   (posit) 1,		/* digitcount */
   (boolean) 0,		/* sign */
   { (digit) 1 }	/* value */
};

static precisionType ptwoConst = {
   (short) 1,		/* refcount (read/write!) */
   (posit) 1,		/* size */
   (posit) 1,		/* digitcount */
   (boolean) 0,		/* sign */
   { (digit) 2 }	/* value */
};

static precisionType p_oneConst = { 
   (short) 1,		/* refcount (read/write!) */ 
   (posit) 1,		/* size */
   (posit) 1,		/* digitcount */
   (boolean) 1,		/* sign */
   { (digit) 1 }	/* value */
};

precision pzero    = &pzeroConst;		/* zero */
precision pone     = &poneConst;		/* one */
precision ptwo     = &ptwoConst;		/* two */
precision p_one    = &p_oneConst;		/* negative one */
