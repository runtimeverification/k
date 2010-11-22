
typedef struct struct_list {
  int hd;
  struct struct_list * tl;
} *list;

#define NULL ((void*)0)

/*@ type plist */

/*@ logic plist nil() */ 

/*@ logic plist cons(list p, plist l) */

/*@ logic plist rev(plist pl) */

/*@ logic plist app(plist l1, plist l2) */

/*@ logic int list_length(plist l) */

/*@ predicate disjoint(plist l1, plist l2) */

/*@ axiom rev_nil_ax : rev(nil()) == nil() */

/*@ axiom app_nil_1_ax : \forall plist l; l == app(l,nil()) */

/*@ axiom app_nil_2_ax : \forall plist l; l == app(nil(),l) */

/*@ axiom disjoint_nil1 : \forall plist l; disjoint(l,nil()) */

/*@ axiom disjoint_nil2 : \forall plist l; disjoint(nil(),l) */


/*@ predicate finite(list l) reads l->tl */

/*@ predicate cyclic(list l) reads l->tl */

/*@ type Length */

/*@ logic Length length(list l) reads l->tl */

/*@ predicate length_order(Length l1, Length l2) */

/*@ predicate lpath(list p1, plist l, list p2) reads p1->tl,\block_length(p1) */

/*@ axiom Path_null_ax : \forall list p; lpath(p,nil(),p) */

/*@ axiom Path_null_inv_ax : 
     \forall list p; \forall plist l; lpath(p,l,p) => l==nil() */

/*@ axiom Path_cons_inv :
     \forall list p1; \forall plist l; \forall list p2;
     (\valid(p1) && lpath(p1->tl,l,p2)) <=> lpath(p1,cons(p1,l),p2) */

/* THE FOLLOWING INVERSION PRINCIPLE MAKES SIMPLIFY LOOP: */
/* @ axiom Path_inv :
      \forall list p1; \forall plist l; \forall list p2;
      lpath(p1,l,p2) => 
         ((p1 == p2 && l == nil()) || 
          (\valid(p1)) && 
	   \exists plist l1; l == cons(p1,l1) && lpath(p1->tl,l1,p2)) */

/*@ predicate llist(list p, plist l) { lpath(p,l,\null) } */ 

/*@ predicate is_list(list l) { \exists plist pl ; llist(l,pl) } */

/*@ axiom is_list_llist_ax :
     \forall list p; is_list(p) <=> \exists plist l; llist(p,l) */

/*@ axiom llist_function_ax :
     \forall plist l1; \forall plist l2; \forall list p;
     llist(p,l1) => llist(p,l2) => l1==l2 */
  
/*@ axiom llist_valid :
     \forall list p1; \forall plist l;
     llist(p1,l) => p1 != \null => \valid(p1) */

