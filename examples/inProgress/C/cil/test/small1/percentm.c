#include <syslog.h>
#include <stdio.h>

int main(void) {
       	syslog(LOG_ERR, "%m");
     	return 0;
}
