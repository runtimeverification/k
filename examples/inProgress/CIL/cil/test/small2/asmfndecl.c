typedef void (*__sighandler_t)  (int)  ;

extern __sighandler_t  
  mysignal(int __sig, __sighandler_t __handler)      
    __asm__ ( "" "__sysv_signal"    ) ;

int main()
{
  // make some use of the signal function so that we don't drop it
  mysignal(5, (__sighandler_t)0);
  return 0;
}

