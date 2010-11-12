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


//////// Instrument a precondition for all functions /////////
__requires(__lock_value(pmutex) == 0)
     __instrument_universal_all
     __instrument_universal_exclude("pfunc*")
     __instrument_universal_exclude("acquire_lock")
     __instrument_universal_exclude("try_acquire_lock")
     __instrument_universal_exclude("release_lock")
     void __instrument_mutex_not_held(){}
/////////////////////////////////////////////////////////////



int data;

///////// Data protected by pmutex //////////////
__requires(__lock_value(pmutex) == 1)
__instrument_read_pre(data)
void __instrument_holds_lock();
/////////////////////////////////////////////////

void locks5_good(int flag)
{
    int value = 0;
    acquire_lock(pmutex);
    value = data;
    release_lock(pmutex);
}

void locks6_bad(int flag)
{
    int value = 0;
    if (flag)
        acquire_lock(pmutex);
    value = data;
    if (flag)
        release_lock(pmutex);
}

//don't instrument pfunc since pmutex might be held
__requires (flag != 0 ==> __lock_value(pmutex) == 1)
__modifies_lock_value(pmutex)
void pfunc_good(int flag)
{
  if (flag)
    release_lock(pmutex);
}

