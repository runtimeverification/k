
#include "testharness.h"


struct new_utsname {
	char sysname[65];
	char nodename[65];
	char release[65];
	char version[65];
	char machine[65];
	char domainname[65];
};

extern struct new_utsname system_utsname;

extern struct rw_semaphore uts_sem;


int Version_132101     ;

struct new_utsname system_utsname = {
	"Linux" , "(none)" , "2.4.5" , "#24 Fri Nov 16 21:05:13 PST 2001" ,
	"i386"  , "(none)" 
};

const char *linux_banner = 
	"Linux version " "2.4.5"  " (" "necula"  "@"
	"manju"  ") (" "gcc version 2.95.3 20010315 (release)"  ") " "#24 Fri Nov 16 21:05:13 PST 2001"  "\n";



int main() {
  SUCCESS;
}
