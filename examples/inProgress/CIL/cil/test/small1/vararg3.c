#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdarg.h>

#include "testharness.h"

char* progname = "vararg3";
int showmessages = 1;

#pragma ccuredvararg("my_vfprintf", printf(2))
int my_vfprintf(FILE *stream, char const *format, va_list args );

#pragma ccuredvararg("pm_error", printf(1))
void pm_error( char* format, ... )     {
  va_list args;

  va_start( args, format );
  
  fprintf( stderr, "%s: ", progname );
  (void) my_vfprintf( stderr, format, args );
  fputc( '\n', stderr );
  va_end( args );
}


/* Portable mini-vfprintf, for systems that don't have either vfprintf or
** _doprnt.  This depends only on fprintf.  If you don't have fprintf,
** you might consider getting a new stdio library.
*/

int my_vfprintf(FILE *stream, char const *format, va_list vargs ) {
    int n;
    char* ep;
    char fchar;
    char tformat[512];
    int do_long;
    int i;
    long l;
    unsigned u;
    unsigned long ul;
    char* s;
    double d;

    n = 0;
    while ( *format != '\0' )
	{
	if ( *format != '%' )
	    { /* Not special, just write out the char. */
	    (void) putc( *format, stream );
	    ++n;
	    ++format;
	    }
	else
	    {
	    do_long = 0;
	    ep = format + 1;

	    /* Skip over all the field width and precision junk. */
	    if ( *ep == '-' )
		++ep;
	    if ( *ep == '0' )
		++ep;
	    while ( isdigit( *ep ) )
		++ep;
	    if ( *ep == '.' )
		{
		++ep;
		while ( isdigit( *ep ) )
		    ++ep;
		}
	    if ( *ep == '#' )
		++ep;
	    if ( *ep == 'l' )
		{
		do_long = 1;
		++ep;
		}

	    /* Here's the field type.  Extract it, and copy this format
	    ** specifier to a temp string so we can add an end-of-string.
	    */
	    fchar = *ep;
	    (void) strncpy( tformat, format, ep - format + 1 );
	    tformat[ep - format + 1] = '\0';

	    /* Now do a one-argument fprintf with the format string we have
	    ** isolated.
	    */
	    switch ( fchar )
		{
		case 'd':
		if ( do_long )
		    {
		    l = va_arg( vargs, long );
		    n += fprintf( stream, tformat, l );
		    }
		else
		    {
		    i = va_arg( vargs, int );
		    n += fprintf( stream, tformat, i );
		    }
		break;

	        case 'o':
	        case 'x':
	        case 'X':
	        case 'u':
		if ( do_long )
		    {
		    ul = va_arg( vargs, unsigned long );
		    n += fprintf( stream, tformat, ul );
		    }
		else
		    {
		    u = va_arg( vargs, unsigned );
		    n += fprintf( stream, tformat, u );
		    }
		break;

	        case 'c':
		i = (char) va_arg( vargs, int );
		n += fprintf( stream, tformat, i );
		break;

	        case 's':
		s = va_arg( vargs, char* );
		n += fprintf( stream, tformat, s );
		break;

	        case 'e':
	        case 'E':
	        case 'f':
	        case 'g':
	        case 'G':
		d = va_arg( vargs, double );
		n += fprintf( stream, tformat, d );
		break;

	        case '%':
		(void) putc( '%', stream );
		++n;
		break;

		default:
		return -1;
		}

	    /* Resume formatting on the next character. */
	    format = ep + 1;
	    }
	}
    return n;
    }



int main() {
  pm_error("Cucu %s", "Bau");
  SUCCESS;
}
