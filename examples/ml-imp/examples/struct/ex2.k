kmod EX2 is including IMP-SYNTAX
  syntax Id ::= a | b | c | d | x | y | z | t

  syntax Stmts ::= ex2

  syntax ?Int ::= `?a 

macro ex2 = (

  struct a {
     int x; 
     struct a *y;
};
  int *b;
  b = new int;
  struct a *c;
  c = new struct a;
  c->x = 7;
  *b = c->x;
  struct a *d;
  d = new struct a;
  c->y = d;
  b = (c->y)->x;
  (c->y)->x = 9;
  int t;
  t = * (*(c+1));

---  z = 99;  --- to see the last configuration: decomment to stop here

  delete c;
  c->x = 11;
)

endkm

---  // assume <config> 
---                   <env> b |-> [3, &struct a] </env>
---                   <heap> 3 |-> 1:[x, int] 4 |-> 2:[y, &struct a] </heap>
---                   <form>  TrueFormula </form>
---             </config >

---  // assert <config>
---                   <env> a |-> [?a, int] </env>
---                   <heap> ?a |-> 7:[x, int] (?a +Int 1) |-> 2:[y, &struct a]  </heap>
---                   <form> TrueFormula </form> 
---            </config>
