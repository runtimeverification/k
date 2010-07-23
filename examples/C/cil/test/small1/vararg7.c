#include <stdio.h>
#include <stdarg.h>

// abstracted from bind

#define ISC_FORMAT_PRINTF(fmt, args) __attribute__((__format__(__printf__, fmt, args)))

struct mystruct {
  int   i;
  char *s;
};

#define CCURED_PRINTF(fmt) __attribute__((__ccuredvararg__(sizeof(struct mystruct))))
typedef struct dns_rdatacallbacks {
        /*
         * dns_load_master calls this when it has rdatasets to commit.
         */
        long add;
        /*
         * dns_load_master / dns_rdata_fromtext call this to issue a error.
         */
        void    (CCURED_PRINTF(3) *error)(struct dns_rdatacallbacks *,
                                          const char * , ...) 
          ISC_FORMAT_PRINTF(2,3) ; 
        /*
         * dns_load_master / dns_rdata_fromtext call this to issue a warning.
         */
        void    (CCURED_PRINTF(3) *warn)(struct dns_rdatacallbacks *,
                                         const char * , ...) 
          ISC_FORMAT_PRINTF(2,3) ; 

        /*
         * Private data handles for use by the above callback functions.
         */
        void    *add_private;
        void    *error_private;
        void    *warn_private;
} dns_rdatacallbacks_t;

static void
stdio_error_warn_callback(dns_rdatacallbacks_t *, const char *, ...)
  ISC_FORMAT_PRINTF(2, 3);

static void
stdio_error_warn_callback(dns_rdatacallbacks_t *callbacks,
    const char *fmt, ...)
{
  va_list ap;

//   UNUSED(callbacks);

  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fprintf(stderr, "\n");
}

void
dns_rdatacallbacks_init(dns_rdatacallbacks_t *callbacks) {
        callbacks->error = stdio_error_warn_callback;
        callbacks->warn = stdio_error_warn_callback;
}

int foo(dns_rdatacallbacks_t *ptr) {
  stdio_error_warn_callback(ptr,"Does it work %s","if we call it directly?");
  ptr->warn(ptr,"Warning Int %d\n",55); 
  ptr->warn(ptr,"Warning String %s\n","mystring"); 
} 
