// DO NOT CHANGE THIS LINE
// Test that read and readv work.

#include <sys/uio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <string.h>
#include <stdio.h>
#include <errno.h>

#include <sys/types.h>
#include <unistd.h>

#define myassert(I) do { \
  if(!(I)) { \
    printf("%s:%d **************** assertion failure\n", __FILE__, __LINE__); \
    abort(); \
  } \
} while(0)

# define MSG0 "HI THERE"
# define MSG1 "BYE NOW!"
# define TESTFILE "writev_test.tmp"

void delete_file(char *name) {
    if(!(unlink(TESTFILE)==0)) {
        if (errno!=ENOENT) perror("error unlinking");
    }
    errno = 0;
    {
        struct stat s;
        int statval = stat(TESTFILE, &s);
        myassert(statval == -1);
        myassert(errno == ENOENT);
    }
}

void test_writev() {
  int in;
  int out;
  int num_written;
  int num_left;
  char *buf;
  const int size = 8;
  struct iovec iov[2];
  char *dummy;
  iov[0].iov_base = "HI THERE";
  iov[0].iov_len = strlen(iov[0].iov_base);
  myassert(iov[0].iov_len == size);
  dummy = "asdfasdf";           // attempt to break string contiguity
  iov[1].iov_base = "BYE NOW!";
  iov[1].iov_len = strlen(iov[1].iov_base);
  myassert(iov[1].iov_len == size);

  // Get rid of the testfile.
  delete_file(TESTFILE);
  
  out = open(TESTFILE, O_WRONLY | O_TRUNC | O_CREAT, S_IRUSR | S_IWUSR);
  if (out==-1) {
    perror("**** error opening file for writing");
    abort();
  }

  // NOTE: we assume that it maximally flushes the buffers.
  {
  num_written = writev(out, iov, 2);
  myassert(num_written = 2 * size);
  myassert(close(out)==0);
  }
  printf("wrote file\n");

  // check it is what we expect.
  {
  buf = malloc((2*size+1) * sizeof buf[0]);
  in = open(TESTFILE, O_RDONLY);
  myassert(buf!=0);
  if (in==-1) {
    perror("**** error opening file for reading");
    abort();
  }

  // read
  printf("trying to read file\n");
  {
  num_left = 2*size;
  while(num_left) {
    int num_read = read(in, buf+(2*size)-num_left, num_left);
    num_left -= num_read;
  }
  buf[2*size] = '\0';
  myassert(num_left==0);
  myassert(close(in)==0);
  }

  // check it is what we expect.
  // NOTE: strings literals concatenate at compile time
  printf("read:%s:\n", buf);
  myassert(strcmp(buf, MSG0 MSG1)==0);
  printf("success\n");

  // Get rid of the testfile.
  delete_file(TESTFILE);
}
}

int main() {
  printf("test writev\n");
  test_writev();
  return 0;
}
