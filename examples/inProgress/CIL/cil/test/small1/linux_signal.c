#include "testharness.h"
    /* Type of a signal handler.  */
    typedef void (*__sighandler_t)(int);

    #define SIG_DFL ((__sighandler_t)0)     /* default signal handling */
    #define SIG_IGN ((__sighandler_t)1)     /* ignore signal */
    #define SIG_ERR ((__sighandler_t)-1)    /* error return from signal */

    struct sigaction {
            __sighandler_t sa_handler;
            unsigned long sa_flags;
            void (*sa_restorer)(void);
            long sa_mask;               /* mask last for extensibility */
    };

    struct k_sigaction {
            struct sigaction sa;
    };


int main() {
  struct k_sigaction sa;

//  if (sa.sa.sa_handler == SIG_DFL) {
    sa.sa.sa_handler = SIG_IGN;
//  } 
  SUCCESS;
} 
