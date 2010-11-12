
/* persistent union-find */

struct puf {
  struct ref *c;
  struct ref *father;
};
typedef struct puf puf;

/*@ predicate is_parray_N(ref *f) {
  @   is_parray(f) && (\forall int j; \forall int v; In(f,j,v) => 0<=v<N)
  @ }
  @*/

/*@ predicate repr(ref *f, int i, int r) 
    reads 
      f->contents, f->contents->tag, f->contents->idx, f->contents->val,
      f->contents->arr[..], f->contents->next
*/

/*@ axiom repr_def: \forall ref *f; \forall int i; \forall int r;
      repr(f,i,r) <=>
        ((In(f,i,i) && r == i) ||
	 (\exists int j; 0<=j<N && In(f,i,j) && repr(f,j,r)))
*/

/*@ requires is_parray_N(f) && 0<=i<N && \valid(res)
  @ ensures  is_parray_N(\result) && repr(f,i,*res) &&
  @  (\forall int k; \forall int r; \old(repr(f,k,r)) <=> repr(\result,k,r))
  @*/
struct ref *find_aux(struct ref *f, int i, int *res) {
  int fi = get(f, i);
  if (fi == i) {
    *res = i;
    return f;
  } else {
    struct ref *ff = find_aux(f, fi, res);
    return set(ff, i, *res);
  }
}

/*@ predicate is_puf(puf *uf) { 
  @   \valid(uf) && is_parray(uf->c) && is_parray_N(uf->father)
  @ }
  @*/

/*@ requires is_puf(uf) && 0<=i<N
  @ ensures is_puf(uf) && 0<=\result<N && repr(uf->father,i,\result) &&
  @  (\forall int k; \forall int r; 
  @     \old(repr(uf->father,k,r)) <=> repr(uf->father,k,r))
  @*/
int find(struct puf *uf, int i) {
  int r;
  struct ref *f = find_aux(uf->father, i, &r);
  uf->father = f;
  return r;
}

/*@ assigns \nothing
  @ ensures \fresh(\result) && \valid(\result) && 
  @ \forall puf *p; \old(is_puf(p)) => is_puf(p) &&
  @ (\forall puf *p; \forall int i; \forall int r;
  @  \old(repr(p->father,i,r)) => repr(p->father,i,r))
  @*/
struct puf *alloc_puf();

/*@ requires is_puf(uf) && 0<=i<N && 0<=j<N
  @ ensures is_puf(uf) && is_puf(\result) 
  (****
  @  \forall int ii; \forall int jj; \forall int r;
  @    (repr(\result->father,ii,r) && repr(\result->father,jj,r)) <=>
  @    ((\old(repr(uf->father,ii,r)) && \old(repr(uf->father,jj,r))) ||
  @     ((i == ii && j ==
  ****)
  @*/
struct puf *union_(struct puf *uf, int i, int j) {
  int ri = find(uf, i);
  int rj = find(uf, j);
  if (ri != rj) {
    struct puf *res = alloc_puf();
    int ric = get(uf->c, ri);
    int rjc = get(uf->c, rj);
    if (ric > rjc) {
      res->c = uf->c;
      res->father = set(uf->father, rj, ri);
      return res;
    } else if (ric < rjc) {
      res->c = uf->c;
      res->father = set(uf->father, ri, rj);
      return res;
    } else {
      res->c = set(uf->c, ri, ric+1);
      res->father = set(uf->father, rj, ri);
      return res;
    }
  } else
    return uf;
}
