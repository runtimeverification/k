kmod EX2 is including IMP-SYNTAX
  syntax Id ::= a | b | c | d | x | y | z | t | test

  syntax Stmts ::= ex2

  syntax ?Int ::= `?a | `?b | `?b' | `?c | `?c1 | `?c2 | `?d | `?d1 | `?d2 | `?t

macro ex2 = (

  struct a {
     int x; 
     struct a *y;
};

int test()
// pre <config> <env> (.).Map </env> <heap> (.).Map </heap> <form> TrueFormula </form> </config>
// post  <config> 
            <env> 
                b |-> [?b , & int] 
                c |-> [?c , & struct a]
                t |-> [?t , int] 
            </env> 
            <heap> 
                ?b |-> ?b' : [@scalar , int] 
                ?c |-> ?c1 : [x , int]
                (?c +Int 1) |-> ?c2 : [y, & struct a]
            </heap> 
            <form> (?b' === ?t) </form> 
            </config>
{
  int *b;
  b = new int; --- calloc
  struct a *c;
  c = new struct a;
  c->x = 7;
  *b = c->x;
  int t;
  t = *(c);

---  z = 99;  --- to see the last configuration: decomment to stop here
--- delete c;
--- c->x = 11;
}
)

endkm