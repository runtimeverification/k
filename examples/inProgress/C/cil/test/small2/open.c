// testing problem with args to open...

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>      // read, close
#include <stdio.h>       // perror


int main()
{
//  int fd = open("/dev/zero", O_RDONLY, 0);    // must pass 3rd arg (matth: why?)

  int fd = open("./open_test", O_CREAT | O_WRONLY, S_IRUSR);
  char buf = 'a';
  if (fd < 0){
    perror("open(./open_test, O_CREAT | O_WRONLY, S_IRUSR) < 0");
    return 1;
  }

  if (write(fd, &buf, 1) != 1) {
    perror("write(fd, &buf, 1) != 1");
    return 2;
  }
  close(fd);
  buf = 0;

  fd = open("./open_test", O_RDONLY);
  if (fd < 0){
    perror("open(./open_test, O_RDONLY) < 0");
    return 3;
  }

  if (read(fd, &buf, 1) != 1) {
    perror("read(fd, &buf, 1) != 1");
    return 4;
  }
  close(fd);
  if (buf != 'a'){
    perror("read wrong value");
    return 5;
  }

  if (unlink("./open_test") != 0)
  {
    perror("unlink(./open_test) != 0");
    return 6;
  }

  printf("Open Succeeded!\n");
  return 0;
}
