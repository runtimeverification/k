struct timeval {
	int	tv_sec;		 
	int	tv_usec;	 
};

extern struct timeval xtime;


volatile struct timeval xtime __attribute__ ((aligned (16)));

extern void printf(char *, ...);
#define E(n) { printf("Error %d\n", n); return n; }


int main() {
  if((int)&xtime & 0xF != 0) E(1);

  printf("Success\n");
  return 0;
}
