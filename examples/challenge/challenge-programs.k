kmod CHALLENGE-PROGRAMS is including CHALLENGE-SYNTAX

  syntax Id ::= a | b | c | d | e | f | g | h | i | j | k | l | m | n | o | p | q | r | s | t | u | v | w | x | y | z 

  syntax Exp ::= p1
  macro p1 = 3+5

  syntax Exp ::= p2
  macro p2 = (3 <= 5) and not (5.8 <= 1.0)

  syntax Exp ::= p3
  macro p3 = randomBool and true

  syntax Exp ::= p4
  macro p4 = (3 <= 5.2) and not (5.8 <= 1)

  syntax Exp ::= p5
  macro p5 = 3 / 2 + 3 / 2.0

  syntax Stmt ::= p6
  macro p6 = var x,y; y = 1.5 + ++y; print(y);

  syntax Stmt ::= p7
  macro p7 = 
        var n, s, i; 
         n = 100;
         s = 0;
         i = n;
         while 1 <= i do (
           s = s+i;
           i = i+-1;
          )
          print( s / (n+0.0));

  syntax Stmt ::= p8
  macro p8 = var a,n,i,j,t;
          n = 10;
          a = malloc(n);
          n = n+-1;
          i = -1;
          while (++i <= n) do {
            *(a+i) = i;
          }
          i = -1; 
          while (++i <= n) do {
            j = i;
            while (++j <= n) do
              if *(a+i) <= *(a+j) then { 
                 t = *(a+i); 
                 *(a+i) = *(a+j);
                 *(a+j) = t;
              } else {}
            print(*(a+i));
          }
 
 
  syntax Stmt ::= p9
  syntax Id ::= odd | even | odd-calls | even-calls
  macro p9 = var odd,even,odd-calls,even-calls;
          aspect (odd-calls = odd-calls+1;)
          odd = lambda x . (if not(0 <= x) then return even(x+1); else if not(x <= 0) then return even(x+-1); else return false;);
          aspect (even-calls = even-calls+1;)
          even = lambda x . (if not(0 <= x) then return odd(x+1); else if not(x <= 0) then return odd(x+-1); else return true;);
          print(odd(read)); 
          print(even(read));
          print(odd-calls);
          print(even-calls);

  syntax Stmt ::= p10
  macro p10 = print((mu f . lambda x . if 2 <= x then return(f(x+-1) *x ); else return(x);)(10));

--- should evaluate to 0 not to 1 (mu is wrong the way it is)
  syntax Stmt ::= p11
  macro p11 = var y; y = 0; var f; f = lambda x . if (x <= 0) then return y; else {var y; y = 1; return f(x+-1);}; print(f(1));

  syntax Stmt ::= p12
  syntax Id ::= goto | exit
  macro p12 = var goto,n; print(callcc (lambda exit . ((callcc (lambda k . (goto = k;))); if n <= 10 then (n = n+1;) else (exit (n);) return goto(0);)));

  syntax Stmt ::= p13
  macro p13 = var x,y;
           x = 1; y = 0;
           spawn (x = 0;)
           while (1 <= x) do (y = y+1;)
           print(y);
        

  syntax Stmt ::= p14
  macro p14 =  var x; 
                x = 1; 
                spawn (rendezvous 1; print(x); rendezvous 2;)
                spawn (rendezvous 3; print(x); rendezvous 4;)
                print(x);
                x = x+1;
                rendezvous 1;  rendezvous 2;
                x = x+1;
                rendezvous 3; rendezvous 4;
   

  syntax Stmt ::= p15
  macro p15 = var x; 
                x = 1; 
                spawn (x = x+1; rendezvous 1;)
                x = x+1;
                rendezvous 1;
                print(x);
    
  syntax Stmt ::= p16
  macro p16 = var x; 
                x = 1; 
                spawn (acquire 1; x = x+1; release 1; rendezvous 1;)
                acquire 1;
                x = x+1;
                release 1;
                rendezvous 1;
                print(x);
    

  syntax Stmt ::= p17
  macro p17 = var x; 
                x = 1; 
                spawn (acquire 1; rendezvous 1; x = x+1; haltThread;)
                rendezvous 1;
                acquire 1;
                x = x+1;
                release 1;
                print(x);
    

  syntax Stmt ::= p18
  macro p18 = var x,y,z;
                x = 1; 
                y = newAgent(var y; y = receiveFrom parent; 
                     sendSynch me to y; spawn haltAgent; print(receive);); 
                z = newAgent(var z; z = receive; 
                     send 17 to z; print(z););
                send z to y;
 

  syntax Stmt ::= p19
  macro p19 = 
   var n,c,i,x;
   n = 5;
   c = quote(1);
   i = 1;
   x = 10;
   while (i <= n) do (
     c = quote(unquote(c)+x);
     i = i+1;
   )
   print(eval(c));

  syntax Stmt ::= p20
  macro p20 =
   var a,b,c;
   c = 10;
   a = lift c;
   b = quote(quote(unquote(unquote(lift c))));
   print(eval(b));
 

  syntax Stmt ::= p21
  macro p21 = 
   var n,c,i,x;
   n = 5;
   c = quote(1);
   i = 1;
   x = 10;
   while (i <= n) do (
     c = quote(quote(unquote(unquote(c))));
     i = i+1;
   )
   print(eval(c));

  syntax Stmt ::= p22
  macro p22 = 
   var x; 
   x = quote(2); 
   print(eval(quote(1+2+unquote(x)+4+5)));

  syntax Stmt ::= p23
  syntax Id ::= genpow | cube
  macro p23 = {
   var genpow;
   genpow = lambda n . {
              if n <= 0
              then return quote 1;
              else return quote (x * unquote (genpow (n+-1)));
            };
   var cube;
   cube = lambda x . { return eval genpow(3);};
   print cube(5);
   print cube(10);
 }

  syntax Stmt ::= p24
  syntax Id ::= f1 | f2 | fib | loc | cod | sender
  macro p24 =
   var fib,loc;
   fib = newAgent
   {
     var m, c, cod;
     m = receive;
     send & c to head m;
     cod = eval receiveFrom head m;
     aspect cod();
     var f;
     f = mu f . lambda x .
             if x <= 1 then { return x; } else {
               var f1,f2;
               spawn {f1 = f(x+-1); rendezvous & f1;}
               spawn {f2 = f(x+-2); rendezvous & f2;}
               rendezvous & f1; rendezvous & f2;
               return f1+f2;
             };
     send [f(head tail m),c] to head m;
   };
   send [me,5] to fib;
   loc = lift receiveFrom fib;
   send quote (lambda () . {acquire unquote loc; *unquote loc = *unquote loc + 1; release unquote loc;}) to fib;
   print receiveFrom fib;

  syntax Stmt ::= p25 | p26
  syntax Id ::= input | array | fix | split | splitl | merge | mergeSort | selectionSort  | list2array | array2list
              | length | sorting | left | right | mergeSortAgent
  macro p25 = 
    var l, selectionSort, list2array, length, array2list, sorting, mergeSortAgent; 
    l = [10,9,8,7,6,5,4,3,2,1];
    mergeSortAgent = newAgent {
      var split, merge, mergeSort;
      split = lambda l.{
                var t;
                if l==[] then return [[],[]];
                else if tail l == [] then return [[head l],[]];
                     else {t=split(tail tail l);return [head l:head t, head tail l:head tail t];}};
      merge = lambda (left,right).{
                if left==[] then return right;
                else if right==[] then return left;
                else if (head left <= head right) then return head  left:merge(tail left,right);
                else return head right : merge(left, tail right);};
      var m, c, cod;
      m = receive;
      send &c to m;
      cod = eval receiveFrom m;
      aspect cod ( );
      mergeSort = lambda l.{
       if l==[] then return [];
       else if tail l==[] then return l;
       else {
         var t, left, right; t=split(l); 
         spawn {left=mergeSort(head t);rendezvous &left;}
         right=mergeSort(head tail t);
         rendezvous &left;
         return merge(left, right);
       }
      };
      while true do {m=receive; spawn send [mergeSort(head tail m), c] to head m;}
    };
    selectionSort = lambda (a,n).{
      var i,j,t;
      i=0;
      while i+2<=n do {
        j=i+1;
        while j+1<=n do {
          if not(*(a+i)<=*(a+j)) 
          then {t=*(a+i);*(a+i)=*(a+j);*(a+j)=t;}
          else {}
          ++j;
        }
        ++i;
      }
    };
    length = mu length.lambda l.{if l==[] then return 0; else return 1+length(tail l); };
    list2array = lambda l.{
      var a,i; a=malloc length(l);i=0;
      while not(l==[]) do {*(a+i)=head l;l=tail l;++i;}
      return [a,i];
    };
    array2list=lambda(a,n).{if n==0 then return[]; else return *a:array2list(a+1,n+-1);};
    send me to mergeSortAgent;
    var loc;  loc = lift receiveFrom mergeSortAgent;
    send quote(lambda(
).{acquire unquote loc;*unquote loc=*unquote loc+1;release unquote loc;}) to mergeSortAgent;
    send [me,l] to mergeSortAgent;
    sorting=lambda l.{
      var t;t=list2array(l);
      selectionSort(head t, head tail t);
      l=array2list(head t, head tail t);
      free head t;
      return l;
    };
    spawn {send [sorting(l),-1] to me;}
    print receive;
    haltSystem;
 

  syntax Stmt ::= SELECTION-SORT
  macro SELECTION-SORT = 
    length = lambda l . { if l == [] then return 0; else return 1 + length(tail l); };
    array = malloc length(input); n = 0;
    while not(input == []) do { *(array + n) = head input; input = tail input; ++n; }
      i = 0;
      while i+2 <= n do {
        j = i+1;
        while j+1 <= n do  {
          if not(*(array+i) <= *(array+j)) 
          then {t = *(array+i); *(array+i) = *(array+j); *(array+j) = t;}
          else {}
          ++j;
        }
        ++i;
      }
 

--- originally, suppose that the main agent did all the work, using only one thread
  macro p26 = 
    var input, length, array, n, i, j, t, k;
    input = [10,9,8,7,6,5,4,3,2,1];
    SELECTION-SORT
    print (mu fix . lambda (a,n) . {if n == 0 then return []; else return *a : fix(a+1, n+-1); })(array,n);
    free array;


--- now the main agent got smarter: creates a new thread and delegates the work to it
  syntax Stmt ::= p27
  macro p27 = 
    var input, length, array, n, i, j, t, k;
    input = [10,9,8,7,6,5,4,3,2,1];
    callcc lambda k . { spawn {k(0);} haltThread; };
    SELECTION-SORT
    print (mu fix . lambda (a,n) . {if n == 0 then return []; else return *a : fix(a+1, n+-1); })(array,n);
    free array;
    haltSystem;


--- comment
  syntax Exp ::= MERGE-SORT-AGENT
  macro MERGE-SORT-AGENT = newAgent {
      var split, merge, mergeSort;
      split = lambda l . {
                var t;
                if l == [] then return [[],[]];
                else if tail l == [] then return [[head l],[]];
                     else {t = split(tail tail l); return [head l : head t,head tail l : head tail t]; } };
      merge = lambda (left, right) . {
                if left == [] then return right;
                else if right == [] then return left;
                else if (head left <= head right) then return head  left : merge(tail left,right);
                else return head right : merge(left, tail right); };
      var m, c, cod;
      m = receive;
      send & c to m;
      cod = eval receiveFrom m;
      aspect cod();
      mergeSort = lambda l . {
       if l == [] then return [];
       else if tail l == [] then return l;
       else {
         var t, left, right; t = split(l); 
         spawn {left = mergeSort(head t); rendezvous & left;}
         right = mergeSort(head tail t);
         rendezvous & left;
         return merge(left, right);
       }
      };
      while true do { m = receive; spawn send [mergeSort(head tail m), c] to head m; }
    }
 
  
--- now the main agent got even smarter: in addition to creating a new thread and delegating the
--- selection sort work to it, it also creates a new agent running a multi-threaded merge sort, and
--- then waits for whichever finishes first; once the first answer is printed, the system is halted
  syntax Stmt ::= p28
  macro p28 = 
    var input, exit, goto, length, array, n, i, j, t, k, mergeSortAgent;
    input = [];
    callcc lambda exit . { callcc (lambda k . {goto = k;}); i = read; if i == -1 then exit(0); else {input = (i : input); goto(1);}};
    callcc lambda k . {
      spawn {k(0);}
      mergeSortAgent = MERGE-SORT-AGENT;
      send me to mergeSortAgent;
      var loc;  loc = lift receiveFrom mergeSortAgent;
      send quote (lambda () . {acquire unquote loc; *unquote loc = *unquote loc + 1; release unquote loc;}) to mergeSortAgent;
      send [me,input] to mergeSortAgent;
      spawn{ print receive; haltSystem;}
      haltThread;
    };
    SELECTION-SORT
    send (mu fix . lambda (a,n) . {if n == 0 then return []; else return *a : fix(a+1, n+-1); })(array,n) to me;
    free array;
 

  syntax Stmt ::= p29
  syntax Id ::= in
  macro p29 = 
    var in, exit, g, length, array, a, n, i, j, t, x, y, mergeSortAgent;
    in = [];
    callcc lambda k.{
                      callcc lambda k.{g=k;};
                      i=read;
                      if i==9 then k(0); else {in=i:in; g(1);}
                    };
    callcc lambda k . {
    spawn k(0);
    mergeSortAgent = newAgent {var split, merge, mergeSort; 
      split = lambda l . {var t; if l == [] then return [[],[]];
        else if tail l == [] then return [[head l],[]];
        else {t = split(tail tail l); return [head l : head t,head tail l : head tail t];}
      }; 
      merge = lambda (left,right) . {if left == [] then return right; 
        else if right == [] then return left; 
        else if head left <= head right then return head left : merge(tail left,right); 
        else return head right : merge(left,tail right);}; 
      var m, c, cod; 
      m = receive; send & c to m; 
      cod = eval receiveFrom m; aspect cod(); 
      mergeSort = lambda l . {
        if l == [] then return []; 
        else if tail l == [] then return l; 
        else {var t,left,right; 
          t = split(l); 
          spawn {left = mergeSort(head t); rendezvous & left;} 
          right = mergeSort(head tail t); 
          rendezvous & left; return merge(left,right);
        }
      }; 
      while true do {m = receive; spawn send [mergeSort(head tail m),c] to head m;}
     };
     send me to mergeSortAgent; 
     var loc; loc = lift receiveFrom mergeSortAgent; 
     send quote(lambda () . {acquire unquote loc; *unquote loc = *unquote loc + 1; release unquote loc;}) 
       to mergeSortAgent; 
     send [me,in] to mergeSortAgent; 
     spawn {print receive; haltSystem;} 
     haltThread;
    };
    n = (mu length . lambda l . {if l == [] then return 0; else return 1 + length(tail l);})(in);
    array = malloc n; 
    a = array; while not in == [] do {*a = head in; in = tail in; ++a;} 
    i = -1; while ++i + 2 <= n do {
      j = i; while ++j + 1 <= n do {
        if not *(array+i) <= *(array+j) then {
           t = *(array+i); *(array+i) = *(array+j); *(array+j) = t;
        } else {} 
    }} 
    send (mu fix . lambda a,n . {if n == 0 then return []; else return *a : fix(a+1,n+-1);})(array,n) to me; 
    free array;

  syntax Stmt ::= p30
  macro p30 = 
    var i;
    i = 0;
    while (++i <= 3) do {
      newAgent {
        print me;
        barrier;
      };
    }
    barrier;
    print me;


  syntax Stmt ::= p31
  macro p31 = 
    var i;
    i = 0;
    while (++i <= 3) do {
      newAgent {print receive;};
    }
    broadcast 0;

endkm
