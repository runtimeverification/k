typedef int agp_setup;


static int test___0;

static __inline__ unsigned long
jiffies_to_timespec(unsigned long jiffies, struct timespec *value)
{
  return (jiffies % 100 ) * (1000000000L / 100 );
}


int foo(int jiffies) {
  return test___0 + jiffies;
}


float test;

float bar() {
  agp_setup x = 5;
  return x;
}

extern float jiffies;

int agp_setup(void) {
  return 5 + jiffies;
}
