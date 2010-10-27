int sum(int n)
/*@ pre < config > < env > n |-> n0 </ env >
                   < form > @(n0 >=Int 0) </ form > configFrame </ config > */
/*@ post < config > < env > ?rho </ env >
                    < form > returns ((n0 *Int (n0 +Int 1)) /Int 2) </ form >
                    configFrame </ config > */
{
  int s;
  s = 0;
  /*@ invariant < config > 
                < env >
                  n |-> ?n
                  s |-> ((n0 +Int (-Int ?n)) *Int (n0 +Int ?n +Int 1)) /Int 2
                </ env >
                < form > @(?n >=Int 0) /\ @(n0 >=Int 0) </ form >
                configFrame </ config > */
  while (n > 0)
  {
    s += n;
    n -= 1;
  }
  return s;
}

int main()
/*@ pre < config > < env > (.).Map </ env >
                   < heap > (.).Map </ heap >
                   < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env >
                    < heap > ?H </ heap >
                    < form > TrueFormula </ form > </ config > */
{
  int s;
  s = sum(5);
  return 0;
}


/*@ var ?s ?n : ?Int */
/*@ var n0 : FreeInt */
/*@ var ?rho ?H : ?MapItem */
/*@ var configFrame : FreeBagItem */

