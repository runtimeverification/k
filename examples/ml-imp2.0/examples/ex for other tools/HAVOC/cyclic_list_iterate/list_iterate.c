#include <windows.h>
#include "../../../include/havoc.h"

#define MAXSIZE 42
typedef struct _DATA{
  int data; 
  LIST_ENTRY list;
} DATA, *PDATA;

PDATA pdata;

//__declare_havoc_bvar(_H_x); //declares as int
__declare_havoc_bvar_type(_H_x, PLIST_ENTRY); //declares as int


////////////////////////////
// Annotation macro STARTS
////////////////////////////
#define __FlinkField 		__field(PLIST_ENTRY, Flink)
#define __listField  		__field(DATA*, list)
#define __dataField  		__field(PDATA, data)

#define __head        		&pdata->list
#define __first       		pdata->list.Flink

#define __dataPtrSet(S)  	__set_incr(__set_decr(S, __listField), __dataField)

#define __dataPtr(x)         	CONTAINING_RECORD((PLIST_ENTRY)x, DATA, list)
#define __initializedData(x) 	__dataPtr(x)->data == 5

#define __listBtwn(x,y)      	__btwn(__FlinkField, x, y)
#define __list1              	__listBtwn(__first, __head)
#define __list2        		__setminus(__listBtwn(__first, __head), __set(__head))
////////////////////////////
// Annotation macro ENDS
////////////////////////////


__requires (__forall(_H_x, __list1, __dataPtr(_H_x) != 0 && __type(__dataPtr(_H_x), PDATA)))
__requires (__setin(__head, __list1))
     
__ensures (__forall(_H_x, __list2, __initializedData(_H_x)))
     
__modifies (__dataPtrSet(__list1))
void InitializeList() {  
  LIST_ENTRY *iter;

  iter = pdata->list.Flink;

  __loop_invariant(
	__loop_assert (__setin(iter, __list1))
	__loop_assert (__forall(_H_x, __listBtwn(__first, iter), _H_x == iter || __initializedData(_H_x)))
	__loop_modifies (__old(__dataPtrSet(__list1))) 
		   ) 
  while (iter != &pdata->list) {
    PDATA elem = CONTAINING_RECORD(iter, DATA, list);
    elem->data = 5;
    iter = iter->Flink;
  }

} 
