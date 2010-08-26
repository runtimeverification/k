// Some problems with open arrays

typedef struct bitmap {
           unsigned long resident[13];
           int words ;
           int allocated_rest ;
  unsigned long * rest; // Allocated on the heap
} BITMAP ;

typedef struct ornode {
  int  * or_const;            /* A hash for the constants. For simplicity 
                               * we use HASH, although something simpler 
                               * might also do since the hashes are small */
  BITMAP any;                 /* This corresponds to a unification variable */
  BITMAP all;                 /* All of the bits in this subtree */
} ORNODE;

typedef struct andnode {
  int count;                  /* How many clauses in this subtree */
  int arity;                  /* The arity of the constant this belongs to */
  union {
    BITMAP nullary;           /* If arity is 0, then a bitmap of the clauses
                                 that match up till here */
    struct ornode args[0];    /* Allocated at the end of this structure, one
                                 for each argument */
  } u;
} ANDNODE;


static ORNODE root;           /* The root of the tree */
int main_o(ANDNODE *a) {
  ORNODE b = a->u.args[1];
  return 0;
}
