#include "../../../include/havoc.h"


#define __lock_value(m)           __resource("LOCK", m)
#define __modifies_lock_value(m)  __modifies_resource("LOCK", m)

__modifies_lock_value(m)
__requires(__lock_value(m) == 0)
__ensures(__lock_value(m) == 1)
void acquire_lock(struct mutex *m);

__modifies_lock_value(m)
__requires(__lock_value(m) == 1)
__ensures(__lock_value(m) == 0)
void release_lock(struct mutex *m);

__modifies_lock_value(m)
__requires(__lock_value(m) == 0)
__ensures(__return != 0 ==> __lock_value(m) == 1)
__ensures(__return == 0 ==> __lock_value(m) == 0)
int try_acquire_lock(struct mutex *m);

struct mutex *pmutex;

__requires(__lock_value(pmutex) == 0)
void locks0_good(int flag)
{
    acquire_lock(pmutex);
    release_lock(pmutex);
}

__requires(__lock_value(pmutex) == 0)
void locks1_good()
{
    int holds = try_acquire_lock(pmutex);
    if (holds)
        release_lock(pmutex);
}

__requires(__lock_value(pmutex) == 0)
void locks2_bad()
{
    acquire_lock(pmutex);
    acquire_lock(pmutex);
    release_lock(pmutex);
    release_lock(pmutex);
}

__requires(__lock_value(pmutex) == 0)
void locks3_bad()
{
    release_lock(pmutex);
}

__requires(__lock_value(pmutex) == 0)
void locks4_bad(int flag)
{
    acquire_lock(pmutex);
    if (flag)
        return;
    release_lock(pmutex);
}

int data;

__requires(__lock_value(pmutex) == 1)
__instrument_read_pre(data)
void __instrument_holds_lock();

__requires(__lock_value(pmutex) == 0)
void locks5_good(int flag)
{
    int value = 0;
    acquire_lock(pmutex);
    value = data;
    release_lock(pmutex);
}

__requires(__lock_value(pmutex) == 0)
void locks6_bad(int flag)
{
    int value = 0;
    if (flag)
        acquire_lock(pmutex);
    value = data;
    if (flag)
        release_lock(pmutex);
}


