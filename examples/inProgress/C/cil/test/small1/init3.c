// From the linux sources
struct hw_interrupt_type {
	const char * typename;
	void (*startup)(unsigned int irq);
	void (*shutdown)(unsigned int irq);
	void (*handle)(unsigned int irq);
	void (*enable)(unsigned int irq);
	void (*disable)(unsigned int irq);
};

extern struct hw_interrupt_type no_irq_type;

struct irqaction {
	void (*handler)(int, void *);
	unsigned long flags;
	unsigned long mask;
	const char *name;
	void *dev_id;
	struct irqaction *next;
};

typedef struct {
	unsigned int status;			 
	struct hw_interrupt_type *handler;	 
	struct irqaction *action;		 
	unsigned int depth;			 
} irq_desc_t;

#define NR_IRQS 224
irq_desc_t irq_desc[] = { [0 ... NR_IRQS -1] = { 0, &no_irq_type, }};

extern void printf(char *, ...);
#define E(n) {printf("Error %d\n", n); return n;}

int main() {

  if(sizeof(irq_desc) / sizeof(irq_desc[0]) != NR_IRQS) E(1);

  if(irq_desc[0].handler != &no_irq_type) E(2);

  if(irq_desc[NR_IRQS / 2].handler != &no_irq_type) E(2);

  if(irq_desc[NR_IRQS - 1].handler != &no_irq_type) E(2);

  printf("Success\n");
  return 0;
}


// Define the no_irq_type here
struct hw_interrupt_type no_irq_type;
