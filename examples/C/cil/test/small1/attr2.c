
__attribute__ ((regparm(0)))
     int  printk   (const char * fmt, ...)
     __attribute__ ((format (printf, 1, 2)));


  void do_exit(long error_code)
	__attribute__((noreturn)) ;

 __attribute__((noreturn))  void do_exit1(long error_code) ;

        
const char __module_parm_vidmem []	__attribute__((section(".modinfo"))) =	"parm_" "vidmem"   "="   "i"  ;

__attribute__((section(".t1sec"))) char t1[5], t2[6];


/* A pointer toa function that does not return */
void ( * pexit)(int err)  __attribute__((noreturn)) ;



extern int * functional(void) __attribute__((__const__));

int  (*ptr_printk) (const char * fmt, ...)
     __attribute__ ((format (printf, 1, 2)));

struct s{
  int  (*printfun) (const char * fmt, ...)
         __attribute__ ((format (printf, 1, 2)));
};

int main() {
  struct s printstruct = {&printk};
  printk("fooo %s", "bau");
  ptr_printk = &printk;
  ptr_printk("fooo %s", "bau");
  printstruct.printfun("fooo %s", "bau");

  { int k = __module_parm_vidmem[3]; }
  functional();
  do_exit(5);
}
