
in imppp-syntax
in imppp-programs

kmod IMPPP-CONFIGURATION is including IMPPP-SYNTAX + K
  syntax K ::= AExp | BExp | Stmt
  syntax KResult ::= Bool | Int

  configuration
    <T>
      <threads>
        <thread multiplicity="*">
          <k>.K</k>
          <env>.Map</env>
        </thread>
     </threads>
     <store>.Map</store>
     <nextLoc>0</nextLoc>
     <in>.List</in>
     <out>.List</out>
    </T>
endkm

kmod IMPPP-SEMANTICS is including IMPPP-CONFIGURATION
  rule <k>X:Id => I<_/k> <env_>X |-> N:Nat<_/env> <store_>N |-> I:Int<_/store>
  rule I1:Int + I2:Int => I1 +Int I2 [structural] 
  rule I1 / I2 => I1 /Int I2  if I2 =/=Bool 0 [structural]
  rule <k>++X => I +Int 1<_/k> <env_>X|->N<_/env> <store_>N|->(I => I +Int 1)<_/store>
  rule <k>read=>I<_/k> <in>ListItem(I)=>.<_/in>

  rule I1<=I2 => I1 <=Int I2   [structural] 
  rule not T:Bool => notBool T [structural]
  rule true and B:BExp => B    [structural]
  rule false and B => false    [structural]

  rule {} => .  [structural]
  rule I; => .  [structural]
  rule S1:Stmt S2:Stmt => S1~>S2  [structural]
  rule <k>X=I; => .<_/k> <env_>X|->N<_/env> <store_>N|->(_=>I)<_/store>
  rule if  true then S1 else _  => S1 [structural]
  rule if false then _  else S2 => S2 [structural]
  rule <k>while B do S:Stmt => if B then S while B do S else {}<_/k> [structural]
  rule <k>print I; => .<_/k> <out_>. => ListItem(I)</out>
  rule <k>spawn S => .<_/k> <env>Rho</env>
       (. => <thread_> <k>S</k> <env>Rho</env> <_/thread>) [structural]
  rule <thread_><k>.K</k> <_/thread> => . [structural] 
  rule <k>haltThread; ~> _ => .</k> [structural]
  rule <k>var X; => .<_/k> <env>Rho => Rho[N/X]</env> 
       <store_>. => N|->0<_/store> <nextLoc>N => sNat N </nextLoc> [structural]
  rule <k>{S} => S~>env(Rho)<_/k> <env>Rho:Map</env> [structural]

--- Auxiliary operation for environment recovery
  syntax K ::= env Map
  rule env(_)~>env(Rho) => env(Rho) [structural]
  rule <k>env(Rho) => .<_/k> <env>_=>Rho</env> [structural]
endkm

kmod IMPPP is including IMPPP-SEMANTICS + IMPPP-PROGRAMS 
  syntax Bag ::= run ( KLabel ) | run ( KLabel , List{K} )
  rule run(KL:KLabel) => run(KL,.List{K}) [structural]
  rule run(KL,L:List`{K`}) => <T_> <k>KL(.List{K})</k> <in>List(L)</in> <_/T> [structural]
endkm
