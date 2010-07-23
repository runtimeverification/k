#include <stdio.h>
#include <stdarg.h>
#include "testharness.h"

static void
ns_client_logv(void *client, void *category,
           void *module, int level, const char *fmt, va_list ap)
{
        char msgbuf[2048];
        char peerbuf[2048];

        vsnprintf(msgbuf, sizeof(msgbuf), fmt, ap);
        puts(msgbuf); 
}

// You must add this pragma to prevent CCured from infering a bad
// descriptor
#pragma ccuredvararg("ns_client_log", printf(5))
void
ns_client_log(void *client, void *category, void *module, int level,
    const char *fmt, ...)
{
  va_list ap;

  va_start(ap,fmt);
  ns_client_logv(client,category,module,level,fmt,ap);
  va_end(ap); 
}

int main()
{
  int i;

  ns_client_log(NULL, NULL, NULL, 0, 
    "Hello, %s! 2+2=%d\n", "world", 4); 

  return 0; 
} 
