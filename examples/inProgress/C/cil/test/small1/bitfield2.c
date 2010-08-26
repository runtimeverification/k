#include "testharness.h"

typedef struct {
    char x;             // this field is only important for automating
                        // the test, we fail even without it
    unsigned dns_resolved:1;
} uri_components;

typedef struct {
  char x;
} test;
int main() {
    if (sizeof(uri_components) == sizeof(test)) {
        E(1);
    }
    SUCCESS;
}
