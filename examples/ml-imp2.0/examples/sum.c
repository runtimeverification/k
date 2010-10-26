/*@ var ?x ?y ?p : ?Int */
/*@ var ?B ?C : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */

int sum(int n)
/*@ pre < config > < env > n |-> n0 </ env > < heap > (.).Map </ heap > < form > @(n0 >=Int 0) </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > (.).Map </ heap > < form > returns ?s /\ @(?n >=Int 0) /\ @(n0 >=Int 0) </ form > </ config > */
{
  int s;
  s = 0;
/*@ invariant <config> 
              <env> n |-> ?n s |-> (((n0 +Int (-Int ?n)) *Int (n0 +Int ?n +Int 1)) /Int 2) </env>
              <heap> .Heap </heap> 
              <form> @(?n >=Int 0) /\ @(n0 >=Int 0) </form> </config> */
  while (n > 0) {
      s = s + n ;
      n = n - 1 ;
  }

  return s;
}



void main()
/*@ pre < config > < env > (.).Map </ env > < heap > (.).Map </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > ?H </ heap > < form > TrueFormula </ form > </ config > */
{
  int n;
  n = 5;
  int summ;
  summ = sum(n);
}

