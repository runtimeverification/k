#include <windows.h>
#include "../../../include/havoc.h"
#include "../../../include/list.h"
#include <malloc.h>

#define MAXSIZE 42
//#define INFINITE 1000000

typedef struct _DATA DATA, *PDATA;

typedef struct {
  int a;
  PDATA container;
  LIST_ENTRY link;
} TYPEA, *PTYPEA;

typedef struct {
  int a;
  PDATA container;
  LIST_ENTRY link;
} TYPEB, *PTYPEB;


struct _DATA {
  LIST_ENTRY xlist;
  HANDLE xlist_lock;
  LIST_ENTRY ylist;
  HANDLE ylist_lock;
};

PDATA pdata;

__declare_havoc_bvar_type(_H_z, PLIST_ENTRY);

#define __offFlink __field(PLIST_ENTRY,Flink)
#define __offBlink __field(PLIST_ENTRY,Blink)
#define __offlinkA __field(PTYPEA,link)
#define __offlinkB __field(PTYPEB,link)
#define __offaA    __field(PTYPEA, a)
#define __offaB    __field(PTYPEB, a)

#define __listF(h) __btwn(__offFlink, h->Flink, h)
#define __listB(h) __btwn(__offBlink, h->Blink, h)

#define __FlinkPtrs(S) __set_incr(S, __offFlink)
#define __BlinkPtrs(S) __set_incr(S, __offBlink)


/////////////////////////////////
// Generic Dlist invariant starts
/////////////////////////////////
#define dlist_inv1(h) (__pforall(_H_z, &_H_z->Blink->Flink, __listF(h), _H_z->Blink->Flink == _H_z))
#define dlist_inv2(h) (__pforall(_H_z, &_H_z->Flink->Blink, __listF(h), _H_z->Flink->Blink == _H_z))
#define dlist_inv3(h) (__seteq(__listF(h), __listB(h)))
#define dlist_inv4(h) (__setin(h, __listF(h)))

#define dlist_inv(s,h) \
        s(dlist_inv1(h))\
        s(dlist_inv2(h))\
        s(dlist_inv3(h))\
        s(dlist_inv4(h))
/////////////////////////////////
// Generic Dlist invariant ends
/////////////////////////////////

#define list_set(x) (__setminus(__listF(x), __set(x)))
#define xlist_set (list_set(((LIST_ENTRY *)&pdata->xlist)))
#define ylist_set (list_set(((LIST_ENTRY *)&pdata->ylist)))


// correctness invariants for type A
#define type_inv1A(s,x) s(__forall(_H_z, list_set(x), __allocated(CONTAINING_RECORD(_H_z, TYPEA, link))))
#define type_inv2A(s,x) s(__forall(_H_z, list_set(x), CONTAINING_RECORD(_H_z, TYPEA, link) != 0))
#define type_inv3A(s,x) s(__forall(_H_z, list_set(x), __type(CONTAINING_RECORD(_H_z, TYPEA, link), PTYPEA)))
#define data_inv_xlist(s,x) s(__forall(_H_z, list_set(x), CONTAINING_RECORD(_H_z, TYPEA, link)->a >= 0))
#define container_invA(s,x) s(__forall(_H_z, list_set(x), CONTAINING_RECORD(_H_z, TYPEA, link)->container == pdata))


// correctness invariants for type B
#define type_inv1B(s,x) s(__forall(_H_z, list_set(x), __allocated(CONTAINING_RECORD(_H_z, TYPEB, link))))
#define type_inv2B(s,x) s(__forall(_H_z, list_set(x), CONTAINING_RECORD(_H_z, TYPEB, link) != 0))
#define type_inv3B(s,x) s(__forall(_H_z, list_set(x), __type(CONTAINING_RECORD(_H_z, TYPEB, link), PTYPEB)))
#define data_inv_ylist(s,x) s(__forall(_H_z, list_set(x), CONTAINING_RECORD(_H_z, TYPEB, link)->a <= 0))
#define container_invB(s,x) s(__forall(_H_z, list_set(x), CONTAINING_RECORD(_H_z, TYPEB, link)->container == pdata))


#define __xlist_correctness(s, h) \
        dlist_inv(s, h) \
        type_inv1A(s, h) \
        type_inv2A(s, h) \
        type_inv3A(s, h) \
        container_invA(s, h)

#define __ylist_correctness(s, h) \
        dlist_inv(s, h) \
        type_inv1B(s, h) \
        type_inv2B(s, h) \
        type_inv3B(s, h) \
        container_invB(s, h)

#define xlist_correctness(s) \
        __xlist_correctness(s, ((LIST_ENTRY *)&pdata->xlist)) \
        data_inv_xlist(s, ((LIST_ENTRY *)&pdata->xlist))

#define ylist_correctness(s) \
        __ylist_correctness(s, ((LIST_ENTRY *)&pdata->ylist)) \
        data_inv_ylist(s, ((LIST_ENTRY *)&pdata->ylist))

#define correctness(s) \
        s(pdata != 0) \
        s(__allocated(pdata)) \
        xlist_correctness(s) \
        ylist_correctness(s)


//         s(__disjoint(xlist_set, ylist_set)) \



__modifies(&pdata)
__modifies(&pdata->xlist.Flink)
__modifies(&pdata->xlist.Blink)
__modifies(&pdata->ylist.Flink)
__modifies(&pdata->ylist.Blink)
__modifies(&pdata->xlist_lock)
__modifies(&pdata->ylist_lock)
correctness(__ensures)
void Init() {
  pdata = (PDATA) malloc(sizeof(DATA));
  InitializeListHead(&(pdata->xlist));
  InitializeListHead(&(pdata->ylist));

  pdata->xlist_lock = CreateMutex(NULL, FALSE, NULL);
  pdata->ylist_lock = CreateMutex(NULL, FALSE, NULL);
}

__modifies (&(elem->link.Flink->Blink))
__modifies (&(elem->link.Blink->Flink))
__frees(elem)
__requires(__setin(elem, list_set((&pdata->xlist))))
correctness(__requires)
correctness(__ensures)
void RemoveElementFromXlist(PTYPEA elem) {
  DWORD result = WaitForSingleObject(elem->container->xlist_lock, INFINITE);
  RemoveEntryList(&(elem->link));
  ReleaseMutex(elem->container->xlist_lock);
  free(elem);
}


__modifies (&(elem->link.Flink->Blink))
__modifies (&(elem->link.Blink->Flink))
__frees(elem)
__requires(__setin(elem, list_set((&pdata->ylist))))
correctness(__requires)
correctness(__ensures)
void RemoveElementFromYlist(PTYPEB elem) {
  DWORD result = WaitForSingleObject(elem->container->ylist_lock, INFINITE);
  RemoveEntryList(&(elem->link));
  ReleaseMutex(elem->container->ylist_lock);
  free(elem);
}

__modifies (&(pdata->xlist.Blink))
__modifies (__old(pdata->xlist.Blink))
__modifies (&(((TYPEA *)__return)->link.Flink))
__modifies (&(((TYPEA *)__return)->link.Blink))
__modifies (&(((TYPEA *)__return)->a))
__modifies (&(((TYPEA *)__return)->container))
correctness(__requires)
correctness(__ensures)
TYPEA *CreateXlistElement() {
  DWORD result;

  TYPEA *elem = (TYPEA *) malloc(sizeof(TYPEA));

  elem->a = 0;
  elem->container = pdata;
  result = WaitForSingleObject(pdata->xlist_lock, INFINITE);
  InsertTailList(&(pdata->xlist), &(elem->link));
  ReleaseMutex(pdata->xlist_lock);
  return elem;
}

__modifies (&(pdata->ylist.Blink))
__modifies (__old(pdata->ylist.Blink))
__modifies (&(((TYPEB *)__return)->link.Flink))
__modifies (&(((TYPEB *)__return)->link.Blink))
__modifies (&(((TYPEB *)__return)->a))
__modifies (&(((TYPEB *)__return)->container))
correctness(__requires)
correctness(__ensures)
TYPEB *CreateYlistElement() {
  DWORD result;

  TYPEB *elem = (TYPEB *) malloc(sizeof(TYPEB));

  elem->a = 0;
  elem->container = pdata;
  result = WaitForSingleObject(pdata->ylist_lock, INFINITE);
  InsertTailList(&(pdata->ylist), &(elem->link));
  ReleaseMutex(pdata->ylist_lock);
  return elem;
}

__modifies (__set_incr(__set_decr(xlist_set,__offlinkA),__offaA))
correctness(__requires)
correctness(__ensures)
void ProcessXlist() {
  LIST_ENTRY *head = &(pdata->xlist);
  DWORD result = WaitForSingleObject(pdata->xlist_lock, INFINITE);
  LIST_ENTRY *iter = head->Flink;
  TYPEA *elem;

  __loop_invariant(
		   __modifies (__old(__set_incr(__set_decr(xlist_set,__offlinkA),__offaA)))
		   __requires(iter == head || __setin(iter, list_set((&pdata->xlist))))
		   data_inv_xlist(__requires, ((LIST_ENTRY *)&pdata->xlist))
		   )
  while (iter != head) {
    elem = CONTAINING_RECORD(iter, TYPEA, link);
    (elem->a)++;
    iter = iter->Flink;
  }
  ReleaseMutex(pdata->xlist_lock);
}


__modifies (__set_incr(__set_decr(ylist_set,__offlinkB),__offaB))
correctness(__requires)
correctness(__ensures)
void ProcessYlist() {
  LIST_ENTRY *head = &(pdata->ylist);
  DWORD result = WaitForSingleObject(pdata->ylist_lock, INFINITE);
  LIST_ENTRY *iter = head->Flink;
  TYPEB *elem;

  __loop_invariant(
		   __modifies (__old(__set_incr(__set_decr(ylist_set,__offlinkB),__offaB)))
		   __requires(iter == head || __setin(iter, list_set((&pdata->ylist))))
		   data_inv_ylist(__requires, ((LIST_ENTRY *)&pdata->ylist))
		   )
  while (iter != head) {
    elem = CONTAINING_RECORD(iter, TYPEB, link);
    (elem->a)--;
    iter = iter->Flink;
  }
  ReleaseMutex(pdata->ylist_lock);
}


