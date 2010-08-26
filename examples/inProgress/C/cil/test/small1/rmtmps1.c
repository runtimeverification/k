#include "testharness.h"

int system_utsname;

struct nlm_rqst {
	unsigned int		a_flags;	 
	char			a_owner[(sizeof(system_utsname)+10) ];
};


int main() {

  struct nlm_rqst s;
  if(sizeof(s) != sizeof(struct nlm_rqst)) E(1);

  SUCCESS;
}
