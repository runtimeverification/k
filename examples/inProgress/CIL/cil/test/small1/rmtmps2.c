typedef struct { volatile int counter; } atomic_t;

 
static __inline__ int atomic_dec_and_test(atomic_t *v)
{
	unsigned char c;

	__asm__ __volatile__(
		""  "decl %0; sete %1"
		:"=m" (v->counter), "=qm" (c)
		:"m" (v->counter) : "memory");
	return c != 0;
}

struct mm_struct {
	atomic_t mm_users;			 
	atomic_t mm_count;			 
};
 

 
extern inline void  __mmdrop(struct mm_struct *)  __attribute__((regparm(3))) ;
static inline void mmdrop(struct mm_struct * mm)
{
	if (atomic_dec_and_test(&mm->mm_count))
		__mmdrop(mm);
}



inline void __mmdrop(struct mm_struct *mm)
{
  return;
}

 

void mmput(struct mm_struct *mm)
{
  if (atomic_dec_and_test(&mm->mm_users) ) {
    mmdrop(mm);
  }
}

// Just want to check that __mmdrop is not dropped
int main() {
  return 0;
}
