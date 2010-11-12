#include <windows.h>
#include "../../../include/havoc.h"
#include "../../../include/list.h"


////////////////////////////////////////////////////////
// Routines for manipulating circular doubly linked list
////////////////////////////////////////////////////////



__declare_havoc_bvar_type(_H_z, PLIST_ENTRY);

// generic program independent macros
#define __offFlink __field(PLIST_ENTRY, Flink)
#define __offBlink __field(PLIST_ENTRY, Blink)

#define __listF(h) __btwn(__offFlink, h->Flink, h)
#define __listB(h) __btwn(__offBlink, h->Blink, h)

#define __BlinkPtrs(S) __set_incr(S, __offBlink)


//////////////////////////////////////////////////
// Generic Dlist invariant (parameterized by head h)
//////////////////////////////////////////////////
#define dlist_inv1(h) (__pforall(_H_z, &_H_z->Blink->Flink, __listF(h), _H_z->Blink->Flink == _H_z))
#define dlist_inv2(h) (__pforall(_H_z, &_H_z->Flink->Blink, __listF(h), _H_z->Flink->Blink == _H_z))

#define dlist_inv3(h) (__seteq(__listF(h), __listB(h)))
#define dlist_inv4(h) (__setin(h, __listF(h)))

#define dlist_inv5(h) (__allocated(__listF(h)) && __allocated(__BlinkPtrs(__listF(h))))
#define dlist_inv6(h) (__forall(_H_z, __listF(h),  _H_z != 0 && __type(_H_z, PLIST_ENTRY)))

#define __dlist_inv(s,h) \
        s(dlist_inv1(h))\
        s(dlist_inv2(h))\
        s(dlist_inv3(h))\
        s(dlist_inv4(h))\
        s(dlist_inv5(h))\
        s(dlist_inv6(h))\
/////////////////////////////////
// Generic Dlist invariant ends
/////////////////////////////////



// program specific macros
#define __fList      __listF(hd)

//////////////////////////////////////
__dlist_inv(__requires, hd)
     __requires(hd != 0)
     __requires(p != 0)
     __requires (__setin(p, __fList))
     __requires (hd != p)


     __dlist_inv(__ensures, hd)
     __ensures (!__setin(p, __fList))

     __modifies (&p->Flink->Blink)
     __modifies (&p->Blink->Flink)
///////////////////////////////////////
void dlist_remove(PLIST_ENTRY hd, PLIST_ENTRY p) {
  RemoveEntryList(p); 
}

///////////////////////////////////////////
__dlist_inv(__requires, hd)
     __requires(hd != 0)
     __requires(__allocated(&p->Flink))
     __requires(__allocated(&p->Blink))
     __requires(p != 0)
     __requires(! __setin(p, __fList))

     __dlist_inv(__ensures, hd)
     __ensures (__setin(p, __fList))

     __modifies (__old(&p->Flink))
     __modifies (__old(&p->Blink))
     __modifies (__old(&hd->Flink))
     __modifies (__old(&hd->Flink->Blink))
///////////////////////////////////////////
void dlist_insert(PLIST_ENTRY    hd, PLIST_ENTRY p) {
  InsertHeadList(hd, p);
}


