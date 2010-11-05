#include "testharness.h"

typedef int my_int;

int main (void)
{
    int x = 0;
    int b = __builtin_constant_p (x++);

    int arr[];

    __builtin_constant_p (x++);
    
    b = __builtin_constant_p (x++);

    if(! __builtin_constant_p(56 + 34)) { x ++; }
    
    // The x++ should happen only once
    (__extension__ (__builtin_constant_p (x++) ? 0 : x++));

    switch(8) {
      case (__builtin_constant_p (x++) ? x : 8):
        break;
    default:
      E(2);
    }
    
    if(x != 1) E(1);

    //__builtin_types_compat_p
    // http://developer.apple.com/documentation/DeveloperTools/gcc-3.3/gcc/Other-Builtins.html
    if(__builtin_types_compatible_p(char, char*)) E(10);
    if(!__builtin_types_compatible_p(int, my_int)) E(11);


    SUCCESS;
 }
