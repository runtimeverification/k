//# 1 "wchar1.c"
//# 1 "testharness.h" 1
extern int printf(const char *, ...);
extern void exit(int);

 



//# 1 "wchar1.c" 2

//# 1 "/usr/include/stddef.h" 1 3
 







































//# 1 "/usr/include/machine/ansi.h" 1 3
 






































 





















 










 

















 












 




 








typedef	int __attribute__((__mode__(__DI__)))		 __int64_t;
typedef	unsigned int __attribute__((__mode__(__DI__)))	__uint64_t;






 



typedef	__signed char		   __int8_t;
typedef	unsigned char		  __uint8_t;
typedef	short			  __int16_t;
typedef	unsigned short		 __uint16_t;
typedef	int			  __int32_t;
typedef	unsigned int		 __uint32_t;

typedef	int			 __intptr_t;
typedef	unsigned int		__uintptr_t;

 



typedef union {
	char		__mbstate8[128];
	__int64_t	_mbstateL;		 
} __mbstate_t;


# 41 "/usr/include/stddef.h" 2 3


typedef	int 	ptrdiff_t;



typedef	int  	rune_t;





typedef	unsigned int 	size_t;




typedef	int  	wchar_t;










# 2 "wchar1.c" 2


int main() {
  wchar_t *wbase = L"Hello" L", world";
  char * w = (char *)wbase;
  char * s =  "Hello" ", world";
  int i;

  for (i=0; i < 10; i++) {
    if (w[i * sizeof(wchar_t)] != s[i]) {
      { printf("Error %d\n",  1 ); exit( 1 ); } ; 
    } 
    if (w[i * sizeof(wchar_t)+ 1] != 0) {
      { printf("Error %d\n",  2 ); exit( 2 ); } ;
    } 
  }
  { printf("Success\n"); exit(0); } ;
}
