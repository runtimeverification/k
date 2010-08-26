#include "testharness.h"

typedef unsigned int	__kernel_size_t;

typedef __kernel_size_t		size_t;

typedef unsigned int __u32;
typedef __u32 kernel_cap_t;

typedef int	pid_t;

typedef unsigned int __kernel_uid32_t;
typedef unsigned int __kernel_gid32_t;

typedef __kernel_uid32_t uid_t;

typedef __kernel_gid32_t gid_t;

typedef struct {
	unsigned long seg;
} mm_segment_t;

struct list_head {
  struct list_head *next, *prev;
};

typedef struct { int gcc_is_buggy; } spinlock_t;

struct __wait_queue_head {
  spinlock_t  lock;
  struct list_head task_list;

};
typedef struct __wait_queue_head wait_queue_head_t;

struct timer_list {
  struct list_head list;
  unsigned long expires;
  unsigned long data;
  void (*function)(unsigned long);
};

typedef long		clock_t;
struct tms {
  clock_t tms_utime;
  clock_t tms_stime;
  clock_t tms_cutime;
  clock_t tms_cstime;
};


typedef struct {
  unsigned long sig[(64  / 32 ) ];
} sigset_t;


struct i387_fsave_struct {
  long	cwd;
  long	swd;
  long	twd;
  long	fip;
  long	fcs;
  long	foo;
  long	fos;
  long	st_space[20];	 
  long	status;		 
};

struct i387_fxsave_struct {
  unsigned short	cwd;
  unsigned short	swd;
  unsigned short	twd;
  unsigned short	fop;
  long	fip;
	long	fcs;
  long	foo;
  long	fos;
  long	mxcsr;
  long	reserved;
  long	st_space[32];	 
  long	xmm_space[32];	 
  long	padding[56];
} __attribute__ ((aligned (16)));

struct i387_soft_struct {
  long	cwd;
  long	swd;
  long	twd;
  long	fip;
  long	fcs;
  long	foo;
  long	fos;
  long	st_space[20];	 
  unsigned char	ftop, changed, lookahead, no_update, rm, alimit;
  struct info	*info;
  unsigned long	entry_eip;
};

union i387_union {
  struct i387_fsave_struct	fsave;
  struct i387_fxsave_struct	fxsave;
  struct i387_soft_struct soft;
};

struct thread_struct {
  unsigned long	esp0;
  unsigned long	eip;
  unsigned long	esp;
  unsigned long	fs;
  unsigned long	gs;
  
  unsigned long	debugreg[8];   
  
  unsigned long	cr2, trap_no, error_code;
  
  union i387_union	i387;
  
  struct vm86_struct	* vm86_info;
  unsigned long		screen_bitmap;
  unsigned long		v86flags, v86mask, v86mode, saved_esp0;
  
  int		ioperm;
  unsigned long	io_bitmap[32 +1];
};

struct rlimit {
  unsigned long	rlim_cur;
  unsigned long	rlim_max;
};




typedef union sigval {
  int sival_int;
  void *sival_ptr;
} sigval_t;



typedef struct siginfo {
  int si_signo;
  int si_errno;
  int si_code;
  
  union {
    int _pad[((128 /sizeof(int)) - 3) ];
    
    
    struct {
      pid_t _pid;		 
      uid_t _uid;		 
    } _kill;
    
    
    struct {
      unsigned int _timer1;
      unsigned int _timer2;
    } _timer;
    
    
    struct {
      pid_t _pid;		 
      uid_t _uid;		 
      sigval_t _sigval;
    } _rt;
    
    
    struct {
      pid_t _pid;		 
      uid_t _uid;		 
      int _status;		 
      clock_t _utime;
      clock_t _stime;
    } _sigchld;
    
    
    struct {
      void *_addr;  
    } _sigfault;
    
    
    struct {
      int _band;	 
      int _fd;
    } _sigpoll;
  } _sifields;
} siginfo_t;

struct sigpending {
  struct sigqueue *head, **tail;
  sigset_t signal;
};

struct sigqueue {
  struct sigqueue *next;
  siginfo_t info;
};



struct task_struct {
	 


  volatile long state;	 
  unsigned long flags;	 
  int sigpending;
  mm_segment_t addr_limit;	 
  
  
  
  int /*struct exec_domain*/ *exec_domain;
  volatile long need_resched;
  unsigned long ptrace;
  
  int lock_depth;		 
  
  long counter;
  long nice;
  unsigned long policy;
  int /*struct mm_struct */ *mm;
  int has_cpu, processor;
  unsigned long cpus_allowed;

  struct list_head run_list;
  unsigned long sleep_time;
  
  struct task_struct *next_task, *prev_task;
  int /*struct mm_struct */ *active_mm;
  
  
  int /* struct linux_binfmt */ *binfmt;
  int exit_code, exit_signal;
  int pdeath_signal;   
  
  unsigned long personality;
  int dumpable:1;
  int did_exec:1;
  pid_t pid;
  pid_t pgrp;
  pid_t tty_old_pgrp;
  pid_t session;
  pid_t tgid;
  
  int leader;

  struct task_struct *p_opptr, *p_pptr, *p_cptr, *p_ysptr, *p_osptr;
  struct list_head thread_group;
  
  
  struct task_struct *pidhash_next;
  struct task_struct **pidhash_pprev;
  
  wait_queue_head_t wait_chldexit;	 
  int /* struct semaphore */ *vfork_sem;		 
  unsigned long rt_priority;
  unsigned long it_real_value, it_prof_value, it_virt_value;
  unsigned long it_real_incr, it_prof_incr, it_virt_incr;
  struct timer_list real_timer;
  struct tms times;
  unsigned long start_time;
  long per_cpu_utime[1 ], per_cpu_stime[1 ];
  
  unsigned long min_flt, maj_flt, nswap, cmin_flt, cmaj_flt, cnswap;
  int swappable:1;
  
  uid_t uid,euid,suid,fsuid;
  gid_t gid,egid,sgid,fsgid;
  int ngroups;
  gid_t	groups[32 ];
  kernel_cap_t   cap_effective, cap_inheritable, cap_permitted;
  int keep_capabilities:1;
  int /*struct user_struct */ *user;
  
  struct rlimit rlim[11 ];
  unsigned short used_math;
  char comm[16];
  
  int link_count;
  int /*struct tty_struct */ *tty;  
  unsigned int locks;  
  
  int /*struct sem_undo */ *semundo;
  int /*struct sem_queue */ *semsleeping;
  
  struct thread_struct thread;
  
  int /* struct fs_struct */ *fs;
  
  int /* struct files_struct */ *files;
  
  spinlock_t sigmask_lock;	 
  int /* struct signal_struct */ *sig;
  
  sigset_t blocked;
  struct sigpending pending;
  
  unsigned long sas_ss_sp;
  size_t sas_ss_size;
  int (*notifier)(void *priv);
  void *notifier_data;
  sigset_t *notifier_mask;
  
  
  __u32 parent_exec_id;
  __u32 self_exec_id;
  
  spinlock_t alloc_lock;
};


static void __attribute__ ((__section__ (".text.init")))  check_fpu(void)
{
  if (((size_t) &(( struct task_struct  *)0)->  thread.i387.fxsave )  & 15) {
    extern void __buggy_fxsr_alignment(void);
    __buggy_fxsr_alignment();
  }

}


int main() {
  int offset;

  
  offset = &(( struct task_struct  *)0)->  thread.i387.fxsave;
  printf("Offset is: %d\n", offset);
  if (((size_t) &(( struct task_struct  *)0)->  thread.i387.fxsave )  & 15) {
    check_fpu();
    E(1);
  }

  SUCCESS;
}
