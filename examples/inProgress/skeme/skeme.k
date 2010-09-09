in ../../../k-prelude

kmod SKEME-SYNTAX is including PL-INT + PL-RAT + PL-FLOAT + PL-ID + PL-STRING 

  syntax Literal ::=  #t  | #f | #unspecified 
                    | []  | #[]
                    | Int | Float | Rat | #\ Char 

  syntax Exp ::= Literal 
               | Id | { String } 
               | [ List{Exp} ] | #[ List{Exp} ] | [ List{Exp} . Exp ]     

  syntax List{Exp} ::= Exp | .List{Exp} | List{Exp}  List{Exp} [assoc id: .List{Exp} hybrid] 

  syntax Program ::= program(List{Exp}) 

  syntax Id ::= eval | display | set-car! | set-cdr! | = | + | - | * | /
              | call-with-current-continuation | call/cc | car | cdr

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

  syntax Internal ::=   vT | vF | vUnspec | vNil 
                      | vi(Int) | vf(Float) | vr(Rat) | vc(Char)                                            
                      | cons(K,K) | vec(Map) | string(Map) | Builtin 
  
  syntax Builtin ::=   bEval | bDisplay | bSetCar | bSetCdr | bEqual | b+ | b- | b* | b/ 
                     | bCallCC | bCar | bCdr

  syntax List{Id} ::= Id | .List{Id} | List{Id} , List{Id} [assoc id: .List{Id} hybrid]

  syntax Literal ::= #procedure(Closure) | #continuation(Continuation) | #builtin(Builtin)   
  
endkm

kmod SKEME-PROGRAMS is including SKEME-SYNTAX
  syntax List{Exp} ::= bar | foo 

  macro foo = [3][4]
  macro bar = [1 2]
endkm

kmod SKEME-SEMANTICS is including SKEME-INTERNAL

  syntax K ::= Program | Exp | Char | String 
  syntax KResult ::= Internal

  op loc : K -> Rat

  configuration <T> <k>.K</k> 
                    <program> .List </program>
                    <globalEnv>.Map</globalEnv> 
                    <env>  .Map </env> 
                    <store> 
                          .Map
---                       loc(0)  |-> bEval 
---                       loc(1)  |-> bDisplay
---                       loc(2)  |-> bSetCar 
---                       loc(3)  |-> bSetCdr
---                       loc(4)  |-> bEqual 
---                       loc(5)  |-> b+
---                       loc(6)  |-> b- 
---                       loc(7)  |-> b* 
---                       loc(8)  |-> b/ 
---                       loc(9)  |-> bCallCC 
---                       loc(10) |-> bCar 
---                       loc(11) |-> bCdr 
                    </store> 
                    <nextLoc> 0 </nextLoc> 
                    <output> .List </output>
               </T>
endkm

kmod SKEME is including SKEME-SEMANTICS + SKEME-PROGRAMS 
  syntax Bag ::= run( List{K} ) 

     op KLtoL : List{K} -> List 
     eq KLtoL((K:K ,, KL:List{K})) = ListItem(K) KLtoL(KL)  
     eq KLtoL(.List{K}) = .List

  ---intial run macro, this starts interpretation
  macro run(KL:List{K}) = <T_> <program> KLtoL(KL) </program> <_/T>
 
  ---initialize the configuration.  Ideally we could do this where there configuration is declared instead of as a rule 
  rule 
      <globalEnv>  .Map =>
                       eval                           |-> loc(0)                         
                       display                        |-> loc(1)  
                       set-car!                       |-> loc(2) 
                       set-cdr!                       |-> loc(3) 
                       =                              |-> loc(4) 
                       +                              |-> loc(5) 
                       -                              |-> loc(6)  
                       *                              |-> loc(7)  
                       /                              |-> loc(8)  
                       call-with-current-continuation |-> loc(9)   
                       call/cc                        |-> loc(9)   
                       car                            |-> loc(10) 
                       cdr                            |-> loc(11) 
      </globalEnv>
      <store>      .Map => 
                       loc(0)  |-> bEval 
                       loc(1)  |-> bDisplay 
                       loc(2)  |-> bSetCar 
                       loc(3)  |-> bSetCdr
                       loc(4)  |-> bEqual 
                       loc(5)  |-> b+
                       loc(6)  |-> b- 
                       loc(7)  |-> b* 
                       loc(8)  |-> b/ 
                       loc(9)  |-> bCallCC 
                       loc(10) |-> bCar 
                       loc(11) |-> bCdr 
      </store> [structural]


  --- if the k cell is empty, we take the first expression in the program and put it
  --- in the k cell
  rule <k> .K => K </k> <program> ListItem(K) => .List <_/program> [structural] 
endkm

