// brlock.c
// reproduce compile problem with linux lib/brlock.c

typedef struct {
	volatile unsigned int lock;



} rwlock_t;
typedef rwlock_t	brlock_read_lock_t;

enum brlock_indices {
	BR_GLOBALIRQ_LOCK,
	BR_NETPROTO_LOCK,

	__BR_END
};

brlock_read_lock_t __brlock_array[32 ][(((sizeof(brlock_read_lock_t)*__BR_END + (1 << ((5) ) )  -1) & ~((1 << ((5) ) )  -1)) / sizeof(brlock_read_lock_t)) ] =
   { [0 ... 32 -1] = { [0 ... (((sizeof(brlock_read_lock_t)*__BR_END + (1 << ((5) ) )  -1) & ~((1 << ((5) ) )  -1)) / sizeof(brlock_read_lock_t)) -1] = (rwlock_t) { 0x01000000    }  } };
