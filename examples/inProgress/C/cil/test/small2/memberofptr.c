struct posix_header {
  char name[100] ;
  char typeflag ;
  char prefix[155] ;
} ; /*onlytypedef*/
union block {
  struct posix_header header ;
} ; /*onlytypedef*/


enum read_header {
  HEADER_FAILURE,
  HEADER_SUCCESS,
  
} ; /*onlytypedef*/


int read_header(void  )
{
  union block *  header ; /*decdef*/
  static char *  next; /*decdef*/
  struct posix_header *  h; /*decdef*/
  char namebuf[sizeof(h->prefix) + 1] ; /*decdef*/
  return sizeof(namebuf);
}

#include "../small1/testharness.h"

int main () {
  if(read_header() != 156) E(1);
  SUCCESS;
                             
}
