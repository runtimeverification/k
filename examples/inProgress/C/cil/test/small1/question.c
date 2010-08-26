#include "testharness.h"

int main() {
    const char *string = "hello";       // works if you remove const!
    const char *p;
    p = string ? string : "NULL"; 
    SUCCESS;
}
