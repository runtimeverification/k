

typedef struct {
  int tag;
  union {
    char *foo;
    struct {
      int a1;
      int *bar;
    } ptr;
  } u SAFEUNION ;
} U;



   
