require cink-syntax

kmod CINK-PROGRAMS is including CINK-SYNTAX 
  syntax Pgm ::= pList

  syntax Id ::= a | b | c | d | e | i | l 
          | limit | nr | nn | n | p | q | r | s | steps | t | t1 | t2 | x | y | z 
          | swap | aux | sum | next | prim | list | point

  macro pList =
    struct list {
       int x;
       struct list *next;
    };
    struct point {
      int x;
      int y;
    };
    int sum() {
       struct point p;
       p.x = 22;
       p.y = 33;
       return p.x + p.y;
    }
    void p() {
       struct list *prim;
       prim = (struct list *)malloc(1*sizeof(struct list));
       (*prim).x = 77;
 breakpoint;
    }

   int main() {
     printf("%d;", sum());
     p();
   } 
      
endkm

