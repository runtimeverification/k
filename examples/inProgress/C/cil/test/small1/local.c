
typedef struct node {
  struct node *xl_cdr;	/* the cdr pointer */
} NODE;


NODE *** xlstack;

#define rplacd(x,y)	((x)->xl_cdr = (y))


/* bquote1 - back quote helper function */
NODE *bquote1(NODE *expr)
{
  NODE ***oldstk;
  expr->xl_cdr = bquote1(expr->xl_cdr);
  xlstack = oldstk;
  return (expr);
}

