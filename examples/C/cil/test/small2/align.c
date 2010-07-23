
typedef struct {
	volatile unsigned int lock;
} spinlock_t;

typedef struct {
} __attribute__((__aligned__((1 << ((5) ) )  )))  irq_desc_t;
extern irq_desc_t irq_desc [224 ];



int main () {
 return 0;
}
