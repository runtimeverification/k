//===--- list.c --- Test Cases for Bit Accurate Types ---------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a test for simple linked list operation. Data are added to
// and removed from the list. We compare the expected value wehen we
// remove data from the list. 
//
//===----------------------------------------------------------------------===//

#include <stdio.h>
#include <stdlib.h>

typedef int __attribute__ ((bitwidth(9))) int9;
typedef int __attribute__ ((bitwidth(7))) int7;

typedef struct myStruct{int9 x; int7 y; } myStruct;
typedef struct myList{myStruct s; struct myList* next;} myList;

int array[64*3] = {103, 198, 105, 115, 81, 255, 74, 236, 41, 205, 186, 171, 
                   242, 251, 227, 70, 124, 194, 84, 248, 27, 232, 231, 141, 
                   118, 90, 46, 99, 51, 159, 201, 154, 102, 50, 13, 183, 49, 
                   88, 163, 90, 37, 93, 5, 23, 88, 233, 94, 212, 171, 178,
                   205, 198, 155, 180, 84, 17, 14, 130, 116, 65, 33, 61, 220,
                   135, 112, 233, 62, 161, 65, 225, 252, 103, 62, 1, 126, 151,
                   234, 220, 107, 150, 143, 56, 92, 42, 236, 176, 59, 251, 50,
                   175, 60, 84, 236, 24, 219, 92, 2, 26, 254, 67, 251, 250,
                   170, 58, 251, 41, 209, 230, 5, 60, 124, 148, 117, 216, 190,
                   97, 137, 249, 92, 187, 168, 153, 15, 149, 177, 235, 241,
                   179, 5, 239, 247, 0, 233, 161, 58, 229, 202, 11, 203, 208,
                   72, 71, 100, 189, 31, 35, 30, 168, 28, 123, 100, 197, 20,
                   115, 90, 197, 94, 75, 121, 99, 59, 112, 100, 36, 17, 158,
                   9, 220, 170, 212, 172, 242, 27, 16, 175, 59, 51, 205, 227,
                   80, 72, 71, 21, 92, 187, 111, 34, 25, 186, 155, 125, 245
};

void test()
{
  unsigned int i=0;
  unsigned int cnt = sizeof(array)/sizeof(*array);

  myList* head = 0;

    
  for(i; i<cnt; ++i)
  {
    myList* elem = malloc(sizeof(myList));

    elem->next = head;
    head = elem;
    (*elem).s.x = array[i];
    (*elem).s.y = array[i] - 1;
  }


  i = 0;
  while(head)
  {
    myList* tmp;
    i+=1;
    if(head->s.x != array[64*3 - i])
      printf("error: i = %d, x = %d, array = %d\n",
             i,head->s.x, array[64*3 - i]);
    if( (head->s.y ^ (int7)((array[64*3 - i] - 1)&0x7f)) != 0 )
      printf("error: i = %d, y = %hhd, expected = %hhd\n",
             i, (unsigned char)(head->s.y), ((array[64*3 - i] - 1)&0x7f));
    //remove from the list
    tmp = head;
    head = head->next;
    free(tmp);
  }
        
}

int main()
{
  test();
  return 0;
}
