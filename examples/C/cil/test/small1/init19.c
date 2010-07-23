typedef struct tTimNetAddr {
  int isIPv4;
  union
  {
    int addr;
    struct {double d; int x; } addr6;
  } u;
} tTimNetAddr;

tTimNetAddr isisPolChangePrefixV6 = {
  .isIPv4 = 0,
  .u = {
    .addr6 = {.d = 0.0, .x = 5},
  },
};


int main() {
  return isisPolChangePrefixV6.u.addr6.x != 5;
}
