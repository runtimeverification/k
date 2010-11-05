
typedef struct {
	volatile unsigned int lock;
} spinlock_t;

spinlock_t runqueue_lock __attribute__((__aligned__(32 ),    
	__section__(".data.cacheline_aligned")))  = (spinlock_t) { 1   } ;


int main () {
 return 0;
}
