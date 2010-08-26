#include <alloca.h>

struct elim_table
{
     int foo;
};

struct elim_table reg_eliminate[5];

#define NUM_ELIMINABLE_REGS (sizeof reg_eliminate / sizeof reg_eliminate[0])
static int (*offsets_at)[NUM_ELIMINABLE_REGS];

void reload2 (void)
{
     offsets_at =
	(int (*)[NUM_ELIMINABLE_REGS]) alloca (NUM_ELIMINABLE_REGS);
}

