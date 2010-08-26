#include <stdio.h>    // printf

typedef unsigned int size_t ;
extern void *  memset(void *  __s , int __c , size_t __n ) ;

typedef struct jpeg_compress_struct *  j_compress_ptr ;

struct jpeg_compress_struct {
  struct jpeg_error_mgr *  err ;
};

struct jpeg_error_mgr {
};

void foo(int x)
{
  printf("sizeof is %d\n", x);
}

void jpeg_create_compress(j_compress_ptr cinfo )
{
  struct jpeg_error_mgr *  err = cinfo->err;

  foo(sizeof(struct jpeg_compress_struct ));

  memset((void *  )cinfo, 0, (size_t )((size_t
    )sizeof(struct jpeg_compress_struct )));

  cinfo->err = err;
}

int main()
{
  struct jpeg_compress_struct cinfo;
  jpeg_create_compress(&cinfo);
  return 0;
}
