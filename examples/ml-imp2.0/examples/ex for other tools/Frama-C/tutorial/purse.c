
typedef struct {
  int balance;
} purse;

//@ predicate purse_inv(purse *p) { \valid(p) && p->balance >= 0 }

/*@ requires purse_inv(p) && s >= 0
  @ ensures purse_inv(p) && p->balance == \old(p->balance) + s 
  @*/
void credit0(purse *p,int s) {
  p->balance = p->balance + s;
}

/*@ requires purse_inv(p) && 0 <= s <= p->balance
  @ ensures purse_inv(p) && p->balance == \old(p->balance) - s
  @*/
void withdraw0(purse *p,int s) {
  p->balance = p->balance - s;
}

#if 0
/*@ requires purse_inv(p1) && purse_inv(p2)
  @ ensures \result == 0
  @*/
int test0(purse *p1, purse *p2) {
    p1->balance = 0;
    credit0(p2,100);
    return p1->balance;
}
#endif


/* using assigns clauses */

/*@ requires purse_inv(p) && s >= 0
  @ assigns p->balance
  @ ensures purse_inv(p) && p->balance == \old(p->balance) + s 
  @*/
void credit(purse *p,int s) {
  p->balance = p->balance + s;
}

/*@ requires purse_inv(p) && 0 <= s <= p->balance
  @ assigns p->balance
  @ ensures purse_inv(p) && p->balance == \old(p->balance) - s
  @*/
void withdraw(purse *p,int s) {
  p->balance = p->balance - s;
}


/*@ requires purse_inv(p1) && purse_inv(p2) && p1 != p2
  @ ensures \result == 0
  @*/
int test1(purse *p1, purse *p2) {
    p1->balance = 0;
    credit(p2,100);
    return p1->balance;
}

/* example of memory allocation
 * currently does not work
 */
//@ assigns \nothing ensures \fresh(\result) && purse_inv(\result) 
purse *new_purse();


//@ ensures \result == 150
int test2() {
    purse *p1 = new_purse();
    purse *p2 = new_purse();
    credit(p1,100);
    credit(p2,200);
    withdraw(p1,50);
    withdraw(p2,100);
    return p1->balance + p2->balance;
}




