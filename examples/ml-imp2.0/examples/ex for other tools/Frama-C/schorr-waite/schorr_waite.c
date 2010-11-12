
/* 
 * graph nodes
 */

#define NULL ((void*)0)

typedef struct struct_node {
  unsigned int m :1, c :1;
  struct struct_node *l, *r;
} * node;


/*
 * logical lists of nodes
 */

/*@ type plist */  
/*@ logic plist cons(node p, plist l) */
/*@ predicate in_list(node p,plist stack) */
/*@ predicate pair_in_list(node p1, node p2, plist stack) */


/* 
 * graph reachability, stack
 */
/*@ predicate reachable(node p1, node p2) 
  @   reads p1->r,p1->l 
  @*/


/*@ axiom reachable_refl : \forall node p ; reachable(p,p) */


/*@ predicate unmarked_reachable(node p1, node p2) 
  @   reads p1->r,p1->l,p1->m 
  @*/

/*@ predicate clr_list(node p, plist stack) 
  @   reads p->c,p->l,p->r
  @*/

/*@ predicate reachable_elements(node p, node t, plist s) 
  @   reads p->l,p->r
  @*/ 

/*
 * the complexity measure for termination
 */

//@ type weight_type

/*@ logic weight_type weight(node p, node t) 
  @   reads p->m,p->c,p->l,p->r
  @*/


/* 
 * Schorr-Waite algorithm 
 */

/*@ requires 
  @   (\forall node x; 
  @      x != \null && reachable(root,x) => \valid(x) && ! x ->m)
  @   && \exists plist l; reachable_elements(root,root,l)
  @ ensures 
  @   (\forall node x; \old(x->l) == x->l && \old(x->r) == x->r) 
  @   &&
  @   (\forall node x; \valid(x) && reachable(root,x) => x->m) 
  @   &&
  @   (\forall node x; ! reachable(root,x) => x->m == \old(x->m))
*/
void schorr_waite(node root) {
  node t = root;
  node p = NULL;
  /*@
    @ invariant
    @
    @ (I1 :: \forall node x; \old(reachable(root,x)) => 
    @       reachable(t,x) || reachable(p,x))
    @ &&
    @ (I2 :: \forall node x; x != \null =>  // pourquoi pas && ? 
    @    (reachable(t,x) || reachable(p,x) => 
    @        \old(reachable(root,x)))) 
    @ &&
    @ (I0 :: \exists plist stack;
    @   (I3 :: clr_list(p,stack)) 
    @   &&
    @   (I4 :: \forall node p; in_list(p,stack) => p->m) 
    @   &&
    @   (I5 :: \forall node x; 
    @     \valid(x) && \old(reachable(root,x)) && !x->m =>
    @      unmarked_reachable(t,x) || 
    @      (\exists node y; 
    @         in_list(y,stack) && unmarked_reachable(y->r,x))) 
    @   &&
    @   (I6 :: \forall node x; !in_list(x,stack) =>  
    @         (x->r == \old(x->r) && x->l == \old(x->l))) 
    @   &&
    @   (I7 :: \forall node p1; (\forall node p2;
    @      pair_in_list(p1,p2,cons(t,stack)) => 
    @        (p2->c => \old(p2->l) == p2->l && \old(p2->r) == p1)
    @        &&
    @        (!p2->c => \old(p2->l) == p1 && \old(p2->r) == p2->r)))
    @   &&
    @   (I8 :: \forall node x; 
    @      ! \old(reachable(root,x)) => x->m == \old(x->m))) 
    @
    @ variant weight(p,t) for order_mark_m_and_c_and_stack
    @
    @*/
  /*   I7 aurait pu etre
      (\forall node p1; (\forall node p2;
              pair_in_list(p1,p2,stack) => 
	          (\old(p2->l) == (p2->c ? p2->l : p1)) &&
	          (\old(p2->r) == (p2->c ? p1 : p2->r))))
  */
  while (p != NULL || (t != NULL && ! t->m)) {
    if (t == NULL || t->m) {
      if (p->c) { /* pop */
	node q = t; t = p; p = p->r; t->r = q; 
      } 
      else { /* swing */
	node q = t; t = p->r; p->r = p->l; p->l = q; p->c = 1;
      }
    } 
    else { /* push */
      node q = p; p = t; t = t->l; p->l = q; p->m = 1; p->c = 0;
    }
  }
}
