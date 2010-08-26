
typedef struct {
  int *a[20];
  int b;
} STR;

STR glob;


int main(STR *s) {
  STR loc = glob;

  *s = glob;
  
  return 0;
}

