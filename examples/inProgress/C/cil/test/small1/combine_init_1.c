#include "testharness.h"

//This was a bug in cabs2cil.  Compiling complicated initializers in
//multiple files generated overlapping global names __constr_expr*

struct logger {
  char* s;
  int i;
};

struct logger *event_list_CHASSIS[]= {
    &(struct logger){"redSecondaryCPMStatusChange", 2013},
    &(struct logger){"redRestoreSuccess", 2014},
    &(struct logger){"redRestoreFail", 2015},
    0
};

extern int c2(void), c3(void);
int main() {
  return 0;
}
