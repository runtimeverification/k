in ../../../k-prelude

kmod SKEME-SYNTAX is including PL-INT + PL-RAT + PL-FLOAT + PL-ID + PL-STRING 

  syntax Literal ::=  #t  | #f | #unspecified 
                    | []  | #[]
                    | Int | Float | Rat | #\ Char 

  syntax Exp ::= Literal 
               | Id | { String } 
               | [ List{Exp} ] | #[ List{Exp} ] | [ List{Exp} . Exp ]     

  syntax List{Exp} ::= Exp | .List{Exp} | List{Exp}  List{Exp} [assoc id: .List{Exp}]
  syntax List{Id} ::= Id | .List{Id} | List{Id} , List{Id} [assoc id: .List{Id}]

  syntax Id ::= eval | display | set-car! | set-cdr! 

  macro [ .List{Exp} ] = [] 
  macro #[ .List{Exp} ] = #[]
  macro [EL:List{Exp} . []] = [EL:List{Exp}] 
  macro [EL:List{Exp} . [EL':List{Exp}]] = [EL:List{Exp} EL':List{Exp}] 
  macro [EL:List{Exp} . [EL':List{Exp} . E:Exp]] = [EL:List{Exp} EL':List{Exp} . E:Exp] 

endkm

kmod SKEME-INTERNAL is including K + SKEME-SYNTAX

  syntax Closure  ::=   closure(List{Id}, List{Exp}, Map)
                      | varClosure(List{Id{, Id, List{Exp}, Map)

  syntax Continuation ::= continuation(K, Map)

  syntax Internal ::=   vT | vF | vUnspec
                      | vNil 
                      | vi(Int) | vf(Float) | vr(Rat) | vc(Char)
                                            
                      | cons(K,K) | vec(Map) | string(Map)  
  
  syntax Builtin ::=   bEval | bDisplay | bSetCar | bSetCdr | bEqual | b+ | b- | b* | b/ 
                     | bCallCC | bCar | bCdr

  syntax Literal ::= #procedure(Closure) | #continuation(Continuation) | #builtin(Builtin) 
  
endkm

kmod SKEME-PROGRAMS is including SKEME-SYNTAX
  syntax Exp ::= foo | bar

  macro foo = 1 2
  macro bar = [1 2]
endkm

kmod SKEME-SEMANTICS is including SKEME-INTERNAL

  syntax K ::= List{Exp} | Exp | Char | String
  syntax KResult ::= Internal
  

  configuration <T> <k>.K</k> 
                    <program> .List{Exp} </program>
                    <globalEnv>.Map</globalEnv> 
                    <env>.Map</env> 
                    <store>.Map</store> 
                    <nextLoc> 0 </nextLoc> 
                    <output> .List{Exp} </output>
               </T>
endkm

kmod SKEME is including SKEME-SEMANTICS + SKEME-PROGRAMS 
  syntax Bag ::= run( KLabel ) 

  ---intial run macro, this starts interpretation
  macro run(KL:KLabel) = <T_> <program> KL(.List{K}) </program> <_/T>

  --- if the k cell is empty, we take the first expression in the program and put it
  --- in the k cell
  rule <T_> <k> .K => E:Exp </k> <program> E => .List{Exp} <_/program> <_/T> [structural] 
endkm

