#include <stdio.h>

typedef struct List {
  struct List *Next;
  int Data;
} List;

List Node0 = {0, 5};
List Node1 = {&Node0, 4};
List Node2 = {&Node1, 3};
List Node3 = {&Node2, 2};
List Node4 = {&Node3, 1};
List Node5 = {&Node4, 0};


int main() {
    List *PrevL, *CurL;
    for (PrevL = 0, CurL = &Node5; CurL; PrevL = CurL, CurL = CurL->Next) {
	printf("%d %d\n", CurL->Data, PrevL ? PrevL->Data : -1);
    }
    return 0;
}

