#include "testharness.h"

struct logger {
  char* s;
  int i;
};

struct logger *event_list_CHASSIS_2[]= {
    &(struct logger){"redRestoreSuccess", 2014},
    &(struct logger){"redRestoreFail", 2015},
    0
};
