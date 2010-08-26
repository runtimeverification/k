
// What happens if malloc returns null?

#include "testharness.h"
#include <malloc.h>
#include <sys/resource.h>
#include <unistd.h>

struct list {
  struct list* next;
  int data[1024*10];
};

int main() {
  struct list* p = 0;

  // This test tries to run out of memory.  To avoid annoying other users, 
  // put a 10MB limit on the memory that is allocated to this test.
  const int heapSize = 1024*1024*10;
  struct rlimit limit = {heapSize, heapSize};
  int res = setrlimit(RLIMIT_DATA, &limit);
  if (res != 0){
    printf("***setrlimit didn't work");
  }   

  while(1) {
    //Eventually, malloc returns null.  Hopefully, CCured won't try to
    //dereference it.
    struct list* newp = malloc(sizeof(struct list));
    if (! newp) { break; }
    newp->next = p;
    p = newp;
  }
  SUCCESS;
}

