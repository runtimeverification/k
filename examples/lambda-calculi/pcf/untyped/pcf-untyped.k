load ../../../../k-prelude

kmod PCF-UNTYPED-SYNTAX is including PL-ID + K-LATEX

  syntax Val ::= Bool
               | Nat
               | succ
               | pred
               | zero?

  syntax Exp ::= Val
               | Id
               | Exp Exp            [strict prec 10 gather(E e)]
               | lambda Id . Exp    [latex "\lambda{#1}\mathbin{.}{#2}"]
               | mu Id . Exp        [latex "\mu{#1}\mathbin{.}{#2}"]
               | cond Exp Exp Exp   [strict(1)]

endkm

kmod PCF-UNTYPED-SEMANTICS is including PCF-UNTYPED-SYNTAX + K

  syntax K ::= Exp
  syntax KResult ::= Val

  configuration
    <T>
      <k> .K </k>
      <env> .Map </env>
      <store> .Map </store>
      <nextLoc> 0 </nextLoc>
    </T>

  kvar L N : Nat
  kvar E E' : Exp
  kvar X : Id
  kvar V : Val

  rule succ N => sNat(N)

  rule pred 0 => 0
  rule pred (sNat N) => N

  rule zero? 0 => true
  rule zero? (sNat N) => false

  rule cond true E E' => E
  rule cond false E E' => E'

  kvar Env Env' : Map

  rule <k> X => E <_/k>
       <env_> X |-> L <_/env>
       <store_> L |-> E <_/store>

  syntax Val ::= closure-lambda ( Map , Id , Exp ) [latex "\textsf{closure}_\lambda({#1},{#2},{#3})"]
  rule <k> lambda X . E => closure-lambda(Env, X, E) <_/k>
       <env> Env </env> 

  rule <k> closure-lambda(Env, X, E) V => E ~> env(Env') <_/k>
       <env> Env' =>  Env[L / X] </env>
       <store_> . => L |-> V <_/store>
       <nextLoc> L => sNat L </nextLoc> 

  syntax Exp ::= closure-mu ( Map , Exp ) [latex "\textsf{closure}_\mu({#1},{#2})"]
  rule <k> mu X . E => closure-mu(Env[L / X], E) <_/k>
       <env> Env </env>
       <store_> . => L |-> closure-mu(Env[L / X], E) <_/store>
       <nextLoc> L => sNat L </nextLoc> 

  rule <k> closure-mu(Env, E) => E ~> env(Env') <_/k>
       <env> Env' => Env </env> 

  // environment recovery
  syntax K ::= env ( Map )
  rule <k> V ~> (env(Env) => .) <_/k>
       <env> _ => Env </env>
       [structural]

endkm

kmod PCF-UNTYPED-PROGRAMS is including PCF-UNTYPED-SEMANTICS

  syntax Id ::= a | b | c | d | e | f | g | h | i | j | k | l | m
              | n | o | p | q | r | s | t | u | v | w | x | y | z

  syntax Exp ::= add | multiply | eleven | fibonacci | factorial | fastfactorial
               | even? | incdec | decinc | fibfac | tozero | constf | const1

  syntax Exp ::= pgm001 | pgm002 | pgm003 | pgm004 | pgm005 | pgm006
               | pgm007 | pgm008 | pgm009 | pgm010 | pgm011 | pgm012
               | pgm013 | pgm014 | pgm015 | pgm016 | pgm017 | pgm018
               | pgm019 | pgm020 | pgm021 | pgm022 | pgm023 | pgm024
               | pgm025 | pgm026 | pgm027 | pgm028 | pgm029 | pgm030
               | pgm031 | pgm032 | pgm033 | pgm034 | pgm035 | pgm036
               | pgm037 | pgm038 | pgm039 | pgm040 | pgm041 | pgm042
               | pgm043 | pgm044 | pgm045 | pgm046 | pgm047 | pgm048

  macro add = mu f . lambda x . lambda y . cond (zero? x) y (succ (f (pred x) y))
  macro multiply = mu f . lambda x . lambda y . cond (zero? x) 0 (add (f (pred x) y) y)

  macro pgm001 = multiply 7 9
  macro pgm002 = multiply (succ (succ (succ 0))) (pred (succ 0))
  macro pgm003 = add 1 (multiply 0 3)
  macro pgm004 = (lambda x . zero? (multiply x 0)) 42
  macro pgm005 = (lambda f . f 5 6) add
  macro pgm006 = (lambda f . f 5 6) multiply
  macro pgm007 = (lambda f . lambda g . g (f 5 6) 7) multiply add
  macro pgm008 = (lambda f . lambda g . g (f 5 6) 7) add multiply

  macro eleven = (lambda s . lambda z . (s (s (s (s (s (s (s (s (s (s (s z))))))))))))
  macro pgm009 = (succ (succ (succ (succ (succ (succ (succ 0)))))))
  macro pgm010 = eleven succ 0
  macro pgm011 = eleven (lambda x . add x 2) 0
  macro pgm012 = eleven (lambda x . multiply 2 x) 1 // SLOW! ~31 seconds on my machine

  macro fibonacci = mu f . lambda x . cond (zero? x) 0 (cond (zero? (pred x)) 1 (add (f (pred x)) (f (pred (pred x)))))
  macro pgm013 = fibonacci 0
  macro pgm014 = fibonacci 5
  macro pgm015 = fibonacci 10

  macro factorial = mu f . lambda x . cond (zero? x) 1 (multiply x (f (pred x)))
  macro pgm016 = factorial 0
  macro pgm017 = factorial 3
  macro pgm018 = factorial 6 // SLOW! ~30 seconds on my machine

  syntax Exp ::= fastmultiply Exp Exp [strict]
  rule fastmultiply N:Nat M:Nat => N:Nat *Nat M:Nat

  macro fastfactorial = mu f . lambda x . cond (zero? x) 1 (fastmultiply x (f (pred x)))
  macro pgm019 = fastfactorial 0
  macro pgm020 = fastfactorial 1
  macro pgm021 = fastfactorial 6
  macro pgm022 = fastfactorial 10
  macro pgm023 = fastfactorial 100
  macro pgm024 = fastfactorial 1000 // ~2 seconds

  macro even? = mu f . lambda x . cond (zero? x) true (cond (f (pred x)) false true)
  macro pgm025 = even? 0
  macro pgm026 = even? 3
  macro pgm027 = even? 4
  macro pgm028 = even? 9

  macro incdec = lambda y . cond (even? y) (lambda x . succ x) (lambda x . pred x)
  macro pgm029 = incdec 1 7
  macro pgm030 = incdec 2 7

  macro decinc = lambda y . cond (even? y) pred succ
  macro pgm031 = decinc 1 7
  macro pgm032 = decinc 2 7

  macro fibfac = lambda x . cond (even? x) fibonacci factorial
  macro pgm033 = fibfac 1 5
  macro pgm034 = fibfac 2 5
  macro pgm035 = fibfac 8 10

  macro tozero = mu f . lambda x . cond (zero? x) x (f (pred x))
  macro pgm036 = tozero 0
  macro pgm037 = tozero 1
  macro pgm038 = tozero 10
  macro pgm039 = tozero (succ (succ (succ 0)))
  
  macro constf = mu f . lambda x . cond true false true
  macro pgm040 = constf true
  macro pgm041 = constf 0
  macro pgm042 = constf constf
  macro pgm043 = constf (mu f . f) // should not terminate since call-by-value

  macro const1 = mu a . mu b . mu c . mu d . lambda x . mu e . mu f . mu g . succ 0
  macro pgm044 = mu a . mu b . mu c . mu d . mu e . mu f . mu g . succ 0
  macro pgm045 = const1 false
  macro pgm046 = const1 (pred 0)
  macro pgm047 = const1 (constf const1)
  macro pgm048 = pred (const1 (mu f . f)) // should not terminate

endkm

kmod PCF-UNTYPED is including PCF-UNTYPED-PROGRAMS

  // operator for running the semantics
  syntax Bag ::= [[ KLabel ]] [latex "\llbracket\,{#1}\,\rrbracket"]
  macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>

  syntax KResultLabel ::= getResult Bag
  macro getResult <T_> <k> KR:KResultLabel(.List{K}) </k> <_/T> = KR

endkm
