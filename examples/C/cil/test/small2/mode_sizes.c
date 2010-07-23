// mode_sizes.c
// demonstrate a problem with 'ping'

// /usr/include/sys/types.h, around line 177, after macro expansion
typedef int int8_t __attribute__ ((__mode__ (  __QI__ ))) ;
typedef int int16_t __attribute__ ((__mode__ (  __HI__ ))) ;
typedef int int32_t __attribute__ ((__mode__ (  __SI__ ))) ;
typedef int int64_t __attribute__ ((__mode__ (  __DI__ ))) ;

typedef unsigned int u_int8_t __attribute__ ((__mode__ (  __QI__ ))) ;
typedef unsigned int u_int16_t __attribute__ ((__mode__ (  __HI__ ))) ;
typedef unsigned int u_int32_t __attribute__ ((__mode__ (  __SI__ ))) ;
typedef unsigned int u_int64_t __attribute__ ((__mode__ (  __DI__ ))) ;

typedef int someInt;      // something I don't want to mess with

typedef short x8_t __attribute__ ((__mode__ (  byte ))) ;

// avoid pulling in conflicting definitions
someInt printf(char const *fmt, ...);

int main()
{
  int ok = 1;

  #define PRSIZE(type, should)                            \
    printf("size of " #type " is: %d (should be %d)\n",   \
           sizeof(type), should); ok = ok && (sizeof(type) == should)
  PRSIZE(int8_t, 1);
  PRSIZE(int16_t, 2);
  PRSIZE(int32_t, 4);
  PRSIZE(int64_t, 8);

  PRSIZE(u_int8_t, 1);
  PRSIZE(u_int16_t, 2);
  PRSIZE(u_int32_t, 4);
  PRSIZE(u_int64_t, 8);

  PRSIZE(x8_t, 1);
  #undef PRSIZE

  return ok? 0 : 1;
}
