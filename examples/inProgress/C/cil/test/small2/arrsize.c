#include "../small1/testharness.h"

// NUMERRORS 8

int g1[-1]; // ERROR(1):Length of array is negative

#define MAXINT (1ull << ((8 * sizeof(int)) - 1))

int g1[ MAXINT / sizeof(int)  ]; //ERROR(2):Length of array is too large
typedef int g1[ MAXINT / sizeof(int) - 1 ];//ERROR(3):Error 3

char g1[ MAXINT / sizeof(char) ]; //ERROR(4):Length of array is too large
typedef char g1[ MAXINT / sizeof(char) - 1  ]; //ERROR(5):Error 5

double g1[ MAXINT / sizeof(double) ]; //ERROR(6):Length of array is too large
typedef double g1[ MAXINT / sizeof(double) - 1  ]; //ERROR(7):Error 7

#if ERROR == 8
struct cmsghdr {
    int cmsg_type;

    __extension__ unsigned char __cmsg_data [];

  };

void os_rcv_fd()
{
        char buf[sizeof(struct cmsghdr)];
}
#endif

int main() {
  g1 *p; E(3); //ERROR(3)
  g1 *p; E(5); //ERROR(5)
  g1 *p; E(7); //ERROR(7)
  E(8); //ERROR(8)
  return 0;
}
