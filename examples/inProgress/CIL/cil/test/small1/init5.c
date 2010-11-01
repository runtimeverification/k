#include "testharness.h"
typedef struct  {
	int gcc_is_buggy ;
} spinlock_t ;

struct list_head {
	struct list_head *  next , *  prev ;
} ;

struct __wait_queue_head {
	spinlock_t lock ;
	struct list_head task_list ;
} ;
typedef struct __wait_queue_head wait_queue_head_t ;


static wait_queue_head_t reiserfs_commit_thread_done = {
  .lock = (spinlock_t){0},
  .task_list = {& reiserfs_commit_thread_done.task_list,
                & reiserfs_commit_thread_done.task_list}
};


int main() {
  if(reiserfs_commit_thread_done.task_list.next !=
     & reiserfs_commit_thread_done.task_list) E(1);

  if(reiserfs_commit_thread_done.task_list.prev !=
     & reiserfs_commit_thread_done.task_list) E(2);

  SUCCESS;
  
}
