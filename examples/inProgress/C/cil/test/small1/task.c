/* this obscure structure definition actually comes up in the linux kernel
 * ... */

typedef struct { } spinlock_t;

struct task_struct {
  spinlock_t sigmask_lock; 
};

struct task_struct my_task;

extern int printf(const char*, ...);

int main() {
  // int *p = (int*) & my_task;
  spinlock_t *sp = & my_task.sigmask_lock;

  printf("Sizeof(mytask) = %d\n", sizeof(my_task));  
  printf("Sizeof(void) = %d\n", sizeof(void));  
  printf("Sizeof(spinlock_t) = %d\n", sizeof(spinlock_t));  
  printf("& (spinlock_t) = %x\n", (long)sp);  
  printf("(& spinlock) + 1 = %x\n", (long)(sp + 1));

  if(sizeof(my_task) != 0) return 1;
  if(sizeof(spinlock_t) != 0) return 2;
  {
    spinlock_t sp1;
    spinlock_t *sp_2 = sp + 1;
    if(sp_2 != sp) return 3;
    *sp_2 = *sp;
  }
  return 0;
}
