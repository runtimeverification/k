#include "../small1/testharness.h"
#include "../small1/testkinds.h"
#include <stdlib.h>

/* weimer 
 * Mon Aug  5 13:28:25 PDT 2002
 * 
 * This represents my best efforts to somehow sneak an integer into a
 * pointer via a void*.
 *
 * Note that derefing such a pointer sometimes gives "ubound" and sometimes
 * gives "reading a pointer that has been tampered with".
 *
 * GN: adjusted to expect Non-pointer error messages.
 */

// NUMERRORS 8

int function() {
#if ERROR == 1
  {
    int i1 = 5;
    void **vi5 = &i1;
    void *vi6 = vi5;
    int * * pi2 = vi5;
    return * * pi2; //ERROR(1):Non-pointer
  }
#endif
#if ERROR == 2
  {
    struct { int a; int b; } c;
    void **v1 = &c;
    void *v2 = v1;
    int **p = v2;
    c.a = 5; 
    return **p; //ERROR(2):Reading
  }
#endif
#if ERROR == 3
  {
    struct { int a; int b; } c;
    void **v1 = &c.b;
    void *v2 = v1;
    int **p = v2;
    c.b = 5; 
    return **p; //ERROR(3):Non-pointer
  }
#endif
#if ERROR == 4
  {
    struct { struct { int a; int b; } c ; int d; } e;
    void **v1 = &e.c.b;
    void *v2 = v1;
    int **p = v2;
    e.c.b = 5; 
    return **p; //ERROR(4):Reading
  }
#endif
#if ERROR == 5
  {
    int i = 5;
    void ****v1;
    void *v2;
    int ****v3;
    v1 = malloc(sizeof(*v1));
    *v1 = malloc(sizeof(**v1));
    **v1 = malloc(sizeof(***v1));
    ***v1 = &i; //ERROR(5):Storing stack address
    v2 = v1;
    v3 = v2; 
    return ****v3; 
  }
#endif
#if ERROR == 6
  {
    int i __HEAPIFY = 5;
    void ****v1;
    void *v2;
    int ****v3;
    v1 = malloc(sizeof(*v1));
    *v1 = malloc(sizeof(**v1));
    **v1 = malloc(sizeof(***v1));
    **v1 = &i; 
    v2 = v1;
    v3 = v2; 
    return ****v3; //ERROR(6):Non-pointer
  }
#endif
#if ERROR == 7
  {
    int i __HEAPIFY = 5;
    void ****v1;
    void *v2;
    int *****v3;
    v1 = malloc(sizeof(*v1));
    *v1 = malloc(sizeof(**v1));
    **v1 = malloc(sizeof(***v1));
    ***v1 = &i; 
    v2 = v1;
    v3 = v2; 
    return *****v3; //ERROR(7):Non-pointer
  }
#endif
#if ERROR == 8
  {
    extern int deref(void *); 
    int (*fptr)(void *) = deref; 
    int x ; 
    x = fptr(5);
  }
#endif
} 

int deref(void *a) {
  int *b = a; 
  return *b; //ERROR(8):Non-pointer
} 

int main() {
  function();
}
