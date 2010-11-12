
/* persistent arrays */

const int N = 100;

/* manually translated from ocaml code */

enum tag { Diff, Array };

struct data;
struct ref { 
  struct data *contents; 
};
struct data { 
  enum tag tag;
  /*should be a union*/
  int idx; int val; struct ref *next;
  int arr[N];
};

typedef struct ref ref;
 
/*@ predicate is_parray(ref *p) 
    reads 
      p->contents, p->contents->tag, p->contents->idx, p->contents->val,
      p->contents->arr[..], p->contents->next */

/*@ axiom is_parray_def:
    \forall ref *p; 
    is_parray(p) <=> 
       (\valid(p) && \valid(p->contents) &&
        (  (p->contents->tag==Array && \valid_range(p->contents->arr,0,N-1))
        || (p->contents->tag==Diff && 0<=p->contents->idx<N &&
            is_parray(p->contents->next))))
*/
 
/*@ predicate In(ref *p, int i, int v) 
    reads 
      p->contents, p->contents->tag, p->contents->idx, p->contents->val,
      p->contents->arr[..], p->contents->next
*/

/*@ axiom In_def:  
      \forall ref *p; \forall int i; \forall int v;
      In(p,i,v) <=>
        (  (p->contents->tag==Array && p->contents->arr[i]==v)
        || (p->contents->tag==Diff && 
            ((p->contents->idx == i && p->contents->val == v) ||
             (p->contents->idx != i && In(p->contents->next,i,v)))))
*/

/*@ requires is_parray(p) && 0<=i<N
  @ ensures In(p,i,\result)
  @*/
int get(ref *p, int i) {
  if (p->contents->tag == Array)
    return p->contents->arr[i];
  else /* Diff */
    if (p->contents->idx == i)
      return p->contents->val;
    else
      return get(p->contents->next,i);
}

/*@ assigns \nothing
  @ ensures \fresh(\result) && \valid(\result) && 
  @ (\forall ref *p; \old(is_parray(p)) => is_parray(p)) &&
  @ (\forall ref *p; \forall int i; \forall int v;
  @  \old(In(p,i,v)) => In(p,i,v))
  @*/
ref *alloc_ref();

/*@ assigns \nothing
  @ ensures \fresh(\result) && \valid(\result) && 
  @ \forall ref *p; \old(is_parray(p)) => is_parray(p) &&
  @ (\forall ref *p; \forall int i; \forall int v;
  @  \old(In(p,i,v)) => In(p,i,v))
  @*/
struct data *alloc_data();

/*@ requires is_parray(p) && 0<=i<N
  @ ensures 
      is_parray(p) 
   && is_parray(\result)
   && (\forall int k; \forall int w; 
       In(\result,k,w) <=> (\old(In(p,k,w)) || (k==i && w==v)))
   && (\forall int k; \forall int w; \old(In(p,k,w)) <=> In(p,k,w))
  @*/
ref* set(ref *p, int i, int v) {
  if (p->contents->tag == Array) {
    int old = p->contents->arr[i];
    //struct data *new_arr = (struct data*)malloc(sizeof(struct data));
    struct data *new_arr = alloc_data();
    //struct data *new_diff = (struct data*)malloc(sizeof(struct data));
    struct data *new_diff = alloc_data();
    //ref *res = (ref*)malloc(sizeof(ref));
    ref *res = alloc_ref();
    //@ assert is_parray(p)
    /* a.(i) <- v */
    p->contents->arr[i] = v;
    /* let res = ref (Array a) */
    res->contents = new_arr;
    new_arr->tag = Array;
    new_arr->arr = p->contents->arr;
    /*@ assert is_parray(res) */
    /* t := Diff (i,old,res) */
    new_diff->tag = Diff;
    new_diff->idx = i;
    new_diff->val = old;
    new_diff->next = res;
    p->contents = new_diff;
    return res;
  } else {
    //struct data *new_diff = (struct data*)malloc(sizeof(struct data));
    struct data *new_diff = alloc_data();
    //ref *res = (ref*)malloc(sizeof(ref));
    ref *res = alloc_ref();
    /*@ assert is_parray(p) */
    /* ref (Diff (i, v, t)) */
    new_diff->tag = Diff;
    new_diff->idx = i;
    new_diff->val = v;
    new_diff->next = p;
    res->contents = new_diff;
    return res;
  }
}
	 
