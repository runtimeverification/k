/*
 * stdarg.h
 *
 * Provides facilities for stepping through a list of function arguments of
 * an unknown number and type.
 *
 * NOTE: Gcc should provide stdarg.h, and I believe their version will work
 *       with crtdll. If necessary I think you can replace this with the GCC
 *       stdarg.h (or is it vararg.h).
 *
 * Note that the type used in va_arg is supposed to match the actual type
 * *after default promotions*. Thus, va_arg (..., short) is not valid.
 *
 * This file is part of the Mingw32 package.
 *
 * Contributors:
 *  Created by Colin Peters <colin@bird.fu.is.saga-u.ac.jp>
 *
 *  THIS SOFTWARE IS NOT COPYRIGHTED
 *
 *  This source code is offered for use in the public domain. You may
 *  use, modify or distribute it freely.
 *
 *  This code is distributed in the hope that it will be useful but
 *  WITHOUT ANY WARRANTY. ALL WARRANTIES, EXPRESS OR IMPLIED ARE HEREBY
 *  DISCLAMED. This includes but is not limited to warranties of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 * $Revision: 1.1.1.1 $
 * $Author: brandon6684 $
 * $Date: 2001/12/18 22:53:51 $
 *
 */
/* Appropriated for Reactos Crtdll by Ariadne */

#ifndef _STDARG_H_
#define _STDARG_H_

#ifndef	_VA_LIST
#define _VA_LIST
typedef char* va_list;
//#endif


/*
 * Amount of space required in an argument list (ie. the stack) for an
 * argument of type t.
 */
// #define __va_argsiz(t)	 (((sizeof(t) + sizeof(int) - 1) / sizeof(int)) * sizeof(int))
// above is for aligned things

#define __va_argsiz(t)	((sizeof(t)))

/*
 * Start variable argument list processing by setting AP to point to the
 * argument after pN.
 */
/*
 * For a simple minded compiler this should work (it works in GNU too for
 * vararg lists that don't follow shorts and such).
 */
#define va_start(ap, pN)	\
	((ap) = ((va_list) (&pN) + __va_argsiz(pN)))


/*
 * End processing of variable argument list. In this case we do nothing.
 */
#define va_end(ap)	((void)0)


/*
 * Increment ap to the next argument in the list while returing a
 * pointer to what ap pointed to first, which is of type t.
 *
 * We cast to void* and then to t* because this avoids a warning about
 * increasing the alignment requirement.
 */

#define va_arg(ap, t)					\
	 (((ap) = (ap) + __va_argsiz(t)),		\
	  *((t*) (void*) ((ap) - __va_argsiz(t))))

#endif /* Not RC_INVOKED */

#endif /* not _STDARG_H_ */
