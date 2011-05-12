

kmod SKEME-SYNTAX is including PL-INT + PL-CONVERSION + PL-ID 

  syntax Literal ::=  #t  | #f | #unspecified 
                    | []  | #[]
                    | Float | Rat | #\ Char 
                    | Rat / Rat

  syntax Exp ::= Literal 
               | Id | String  
               | [ List{Exp} ] | #[ List{Exp} ] | [ List{Exp} * Exp ] | [* Exp ]  
               | `! Exp

  syntax List{Exp} ::= Exp | .List{Exp} | List{Exp}  List{Exp} [assoc id: .List{Exp} strict hybrid] 
  
  op length : List{Exp} -> Int
  eq length(E:Exp EL:List{Exp}) = 1 +Int length(EL)
  eq length(.List{Exp}) = 0  

  syntax Id ::= eval | display | set-car! | set-cdr! | o= | o+ | o- | o* | o/ | o=
              | call-with-current-continuation | call/cc | car | cdr 
              | cons
              | oif | quote | begin | define | lambda | set!
              | x | id( String )

  macro R:Rat / NzR:NzRat = R /Rat NzR
  macro [ .List{Exp} ] = [] 
  macro [ .List{Exp} * E:Exp ] = [* E] 
  macro #[ .List{Exp} ] = #[]
  macro [EL:List{Exp} * []] = [EL:List{Exp}] 
  macro [EL:List{Exp} * [EL':List{Exp}]] = [EL:List{Exp} EL':List{Exp}] 
  macro [EL:List{Exp} * [EL':List{Exp} * E:Exp]] = [EL:List{Exp} EL':List{Exp} * E:Exp] 
  macro ! E:Exp = [quote E]
  macro [define [X:Id EL1:List{Exp}] EL2:List{Exp}]
      = [define X [lambda [EL1] EL2]]
  macro [define [X:Id EL1:List{Exp} * E:Exp] EL2:List{Exp}]
      = [define X [lambda [EL1 * E] EL2]]
endkm

kmod SKEME-INTERNAL is including K + SKEME-SYNTAX

  syntax Closure  ::=   closure( List{Exp} , List{Exp} , Map )
                      | varClosure( List{Exp} , Exp , List{Exp} , Map )

  syntax Continuation ::= continuation( K , Map )

  syntax Internal ::=   vT | vF | vUnspec | vNil 
                      | vf( Float ) | vr( Rat ) | vc( Char ) | vn( Id )                                           
                      | cons( K * K ) | vec( Map # Int ) | string( Map # Int ) | Builtin 
                      | Closure | Continuation
  
  syntax Builtin ::=   bEval | bDisplay | bSetCar | bSetCdr | b+ | b- | b* | b/ | b= 
                     | bCallCC | bCar | bCdr | bCons
  
  syntax List{Internal} ::= Internal | List{Internal} List{Internal} [ditto]
 
  syntax Literal ::= #procedure( Closure ) | #continuation( Continuation ) | #builtin( Builtin )   
  
  syntax Exp ::= Internal
  syntax List{Exp} ::= List{Internal}

endkm

kmod SKEME-PROGRAMS is including SKEME-SYNTAX + SKEME-INTERNAL
  syntax List{Exp} ::= bar | foo | baz | chaz | kraz | apply | apply2 | id-test 
                      | begintest | plustest | plustest2 | timestest
                      | subtest | subtest2
                      | divtest
                      | divtest2
                      | divtest3
                      | divtest4
                      | cartest
                      | cdrtest
                      | setcartest
                      | setcdrtest
                      | setcdrtest2
                      | constest
                      | settest
                      | settest2 --- for when we have local bindings
                      | lambdatest
                      | closuretest
                      | varclosuretest
                      | fac
                      | fac2
                      | envcap
                      | var
                      | var2
                      | call-cc-test


  macro foo = #[]
  macro bar = [display [oif #t "true" "false"]]
  macro baz = #[#[#[3]] "true"]
  macro chaz = [eval ![1 * [2]]]
  macro kraz = ![#[42 [43]] "44"]
  macro apply = [display [define x 3]][display x]
  macro apply2 = [display "true"][display "false"] [display 16]
  macro begintest = [display [begin [display "true"][display "false"] [display 16]]]
  macro id-test = eval
  macro plustest = [display [o+ 1 2 3.4 5]]
  macro plustest2 = [display [o+]]
  macro timestest = [display [o* 1 2 3.4 5]]
  macro subtest = [display [o- 1]]
  macro subtest2 = [display [o- 1 3.4]]
  macro divtest = [display [o/ 3.4]]
  macro divtest2 = [display [o/ 3]]
  macro divtest3 = [display [o/ 10 2 2.1 1]]
  macro divtest4 = [display [o/ (1/3) (1/3)]]
  macro cartest = [display [car ![1 2 3]]]
  macro cdrtest = [display [cdr ![1 2 3]]]
  macro setcartest = [define x ![1 2 3]][display [set-car! x 4]][display x]
  macro setcdrtest = [define x ![1 2 3]][display [set-cdr! x 4]][display x]
  macro setcdrtest2 = [define x ![1 2 3]][display [set-cdr! x ![4 5]]][display x]
  macro constest = [display [cons 1 2]] [define x ![1 2 3]] [display [cons 42 x]]
  macro settest = [define x ![1 2 3]][display [set! x 3]][display x]
  macro lambdatest = [display [lambda [x] [o+ x 3][o+ x 3]]] 
  macro closuretest = [define id("a") 42]
                      [[lambda [id("a") id("b")]  [display [o+ id("a") id("b")]]
                                                  [set! id("a") 50]
                                                  [display id("a")]] 
                        15 10]
                      [display id("a")]
  macro varclosuretest = [define x [lambda [id("z") * id("y")] id("y")]] [display [x 1 2 3]]
  macro fac = [define id("fac") 
                      [lambda [x] 
                                 [oif [o= x 0]
                                      1
                                      [o* x [id("fac") [o- x 1]]]]]]
              [display [id("fac") 6]]
  macro fac2 = [define [id("fac") x] 
                                 [oif [o= x 0]
                                      1
                                      [o* x [id("fac") [o- x 1]]]]]
              [display [id("fac") 6]]

  macro envcap = [define id("nilarg") 0]
                 [define x [lambda [id("y")] [set! id("nilarg") [lambda [] id("y")]]]]
                 [display [x 42]]  
                 [display [id("nilarg")]]
                 [x 512]
                 [display [id("nilarg")]]
  
  macro var = [define [id("foo") id("x") * id("y")] 
                         [display id("x")]
                         [display id("y")]
              ]
              [id("foo") 1 2 3 ![4 5]]
 
  macro var2 = [define [id("list") * id("x")] id("x")]
               [display [id("list") 1 2 3 4 5]]
               [display [id("list")]]
 
  macro call-cc-test = [define id("k") #f]
                       [display [o+ 1 1 1 [call/cc [lambda[id("c")] [set! id("k") id("c")] 0]]]]
                       [id("k") 3]

endkm

kmod SKEME-SEMANTICS is including SKEME-INTERNAL


  syntax K ::= List{Exp} | Char | String 
  syntax KResult ::= Internal

  op loc : K -> K

  configuration <T> <k>.K</k> 
                    <program>   .List </program>
                    <globalEnv> 
                       eval                           |-> loc(-Rat 1)                         
                       display                        |-> loc(-Rat 2)  
                       set-car!                       |-> loc(-Rat 3) 
                       set-cdr!                       |-> loc(-Rat 4) 
                       o=                             |-> loc(-Rat 5) 
                       o+                             |-> loc(-Rat 6) 
                       o-                             |-> loc(-Rat 7)  
                       o*                             |-> loc(-Rat 8)  
                       o/                             |-> loc(-Rat 9)  
                       call-with-current-continuation |-> loc(-Rat 10)    
                       call/cc                        |-> loc(-Rat 10)   
                       car                            |-> loc(-Rat 11) 
                       cdr                            |-> loc(-Rat 12) 
                       cons                           |-> loc(-Rat 13) 
                    </globalEnv> 
                    <env> .Map </env> 
                    <store>     
                       loc(-Rat 1)  |-> bEval 
                       loc(-Rat 2)  |-> bDisplay 
                       loc(-Rat 3)  |-> bSetCar 
                       loc(-Rat 4)  |-> bSetCdr
                       loc(-Rat 5)  |-> b= 
                       loc(-Rat 6)  |-> b+
                       loc(-Rat 7)  |-> b- 
                       loc(-Rat 8)  |-> b* 
                       loc(-Rat 9)  |-> b/ 
                       loc(-Rat 10) |-> bCallCC 
                       loc(-Rat 11) |-> bCar 
                       loc(-Rat 12) |-> bCdr 
                       loc(-Rat 13) |-> bCons 
                    </store> 
                    <nextLoc> 0 </nextLoc> 
                    <output> .List </output>
                    <keywords> 
                       SetItem(oif) 
                       SetItem(quote) 
                       SetItem(begin) 
                       SetItem(define) 
                       SetItem(lambda) 
                       SetItem(set!) 
                    </keywords>
               </T>

  op bind : List{Exp} List{Exp} -> K
  op varBind : List{Exp} Exp List{Exp} -> K
  op consify : List{Exp} -> Internal
  op restore : Map -> K

  --- rules for binding variables for closure application
  rule <k>       bind(X:Id XL:List{Exp}, I:Internal IL:List{Internal}) 
             =>  bind(XL, IL)
       <_/k>
       <env_>   .Map => X |-> loc(Loc:Rat) </env>
       <store_> .Map => loc(Loc) |-> I   </store> 
       <nextLoc> Loc => Loc +Rat 1     </nextLoc> [structural]
 
  rule bind(.List{Exp}, .List{Exp}) => .K [structural]
  
  --- rules for variardic binding
  rule <k>       varBind(X:Id XL:List{Exp}, X':Id, I:Internal IL:List{Internal}) 
             =>  varBind(XL, X', IL)
       <_/k>
       <env_>   .Map => X |-> loc(Loc:Rat) </env>
       <store_> .Map => loc(Loc) |-> I   </store> 
       <nextLoc> Loc => Loc +Rat 1     </nextLoc> [structural]

  rule <k> varBind(.List{Exp}, X:Id, .List{Exp}) => .K <_/k>
       <env_>   .Map => X        |-> loc(Loc)  </env>
       <store_>  .Map => loc(Loc) |-> vNil      </store>
       <nextLoc>  Loc => Loc +Rat 1  </nextLoc>
       [structural]

  rule <k> varBind(.List{Exp}, X:Id, I:Internal IL:List{Internal}) => .K <_/k>
       <env_>     .Map => X |-> loc(Loc)  </env>
       <store_>   .Map => 
            loc(Loc)        |-> cons(loc(Loc +Rat 1) * loc(Loc +Rat 2))
            loc(Loc +Rat 1) |-> I       
            loc(Loc +Rat 2) |-> consify(IL)      
       </store>
       <nextLoc>  Loc => Loc +Rat 3  </nextLoc>
       [structural]

  rule consify(.List{Exp}) => vNil [structural]
  
  rule <store_> loc(Loc':Rat)    |-> consify(I:Internal IL:List{Internal}) 
             =>
                loc(Loc')        |-> cons(loc(Loc) * loc(Loc +Rat 1))
                loc(Loc)         |-> I       
                loc(Loc +Rat 1)  |-> consify(IL) 
       </store>
       <nextLoc>  Loc => Loc +Rat 2  </nextLoc>  
       [structural]  


  --- restoring the environment
  rule <k> I:Internal ~> (restore(Env:Map) => .K) <_/k>
       <env> _ => Env </env> [structural]
endkm

kmod INTERN is including SKEME-SEMANTICS
  op intern  : K                  -> K
  op internS : KResult String Nat -> K  
  op internV : KResult K Nat      -> K

  --- interning for literals    
  rule intern(#t)           => vT            [structural]
  rule intern(#f)           => vF            [structural]
  rule intern(#unspecified) => vUnspec       [structural]
  rule intern(ID:Id)        => vn(ID)        [structural]
  rule intern(F:Float)      => vf(F)         [structural]
  rule intern(R:Rat)        => vr(R)         [structural]
  rule intern(#\C:Char)     => vc(C)         [structural]
  rule intern([])           => vNil          [structural]
  rule intern(#[])          => vec(.Map # 0) [structural]
  rule intern([* E:Exp])    => intern(E)     [structural]

  --- intern Closure
  rule intern(#procedure(Cl:Closure)) => Cl    [structural]

  --- intern Continuation
  rule intern(#continuation(Co:Continuation)) => Co    [structural]

  --- interning String
  rule intern( Str:String ) => internS(string(.Map # lengthString(Str)), Str, 0) [structural]  

  rule internS(KR:KResult, Str, _) => KR if lengthString(Str) ==Bool 0 [structural]

  --- k level interning String
  rule <k_> 
           internS(
             string(
               (M:Map => M:Map Pos:Nat |-> loc(Loc:Rat)) # _
             ), 
             (Str => substrString(Str, 1, lengthString(Str))), 
             (Pos => Pos +Nat 1)
           )
       <_/k>   
       <nextLoc> Loc => Loc +Rat 1 </nextLoc>
       <store> .Map => loc(Loc) |-> substrString(Str, 0, 1) <_/store> 
       if lengthString(Str) =/=Bool 0 [structural] 

  --- store level interning String
  rule <store>
         loc(Loc':Rat) |->  
           internS(
             string(
               (M:Map => M:Map Pos:Nat |-> loc(Loc:Rat)) # _
             ), 
             (Str => substrString(Str, 1, lengthString(Str))), 
             (Pos => Pos +Nat 1)
           )
         (.Map => loc(Loc) |-> substrString(Str, 0, 1))
       <_/store> 
       <nextLoc> Loc => Loc +Rat 1 </nextLoc>
       if lengthString(Str) =/=Bool 0 [structural] 

  --- interning Vectors
  rule intern( #[EL:List{Exp}] ) => internV(vec(.Map # length(EL)), EL, 0) [structural]

  rule internV(KR:KResult, .List{Exp}, _) => KR [structural]

  --- k level interning Vectors
  rule <k_> 
           internV(
             vec(
               (M:Map => M:Map Pos:Nat |-> loc(Loc:Rat)) # _
             ), 
             (E:Exp EL:List{Exp} => EL), 
             (Pos => Pos +Nat 1)
           )
       <_/k>   
       <nextLoc> Loc => Loc +Rat 1 </nextLoc>
       <store> .Map => loc(Loc) |-> intern(E) <_/store> [structural] 

  --- store level interning Vectors
  rule <store>
         loc(Loc':Rat) |->  
           internV(
             vec(
               (M:Map => M:Map Pos:Nat |-> loc(Loc:Rat)) # _
             ), 
             (E:Exp EL:List{Exp} => EL), 
             (Pos => Pos +Nat 1)
           )
         (.Map => loc(Loc) |-> intern(E))
       <_/store> 
       <nextLoc> Loc => Loc +Rat 1 </nextLoc> [structural] 

  --- interning Lists
  rule <k_>
         intern([E:Exp EL:List{Exp}]) => cons(loc(Loc) * loc(Loc +Rat 1))
       <_/k>
       <nextLoc> Loc => Loc +Rat 2 </nextLoc>
       <store> .Map => loc(Loc) |-> intern(E) loc(Loc +Rat 1) |-> intern([EL]) <_/store> [structural] 
  
  rule <store>
         loc(Loc':Rat) |->
           (intern([E:Exp EL:List{Exp}]) => cons(loc(Loc) * loc(Loc +Rat 1)))
         (.Map => loc(Loc) |-> intern(E) loc(Loc +Rat 1) |-> intern([EL]))
       <_/store>
       <nextLoc> Loc => Loc +Rat 2 </nextLoc> [structural]


  --- interning imperfect Lists
  rule <k_>
         intern([E:Exp EL:List{Exp} * E':Exp]) => cons(loc(Loc) * loc(Loc +Rat 1))
       <_/k>
       <nextLoc> Loc => Loc +Rat 2 </nextLoc>
       <store> .Map => loc(Loc) |-> intern(E) loc(Loc +Rat 1) |-> intern([EL * E']) <_/store> [structural] 
  
  rule <store>
         loc(Loc':Rat) |->
           (intern([E:Exp EL:List{Exp} * E':Exp]) => cons(loc(Loc) * loc(Loc +Rat 1)))
         (.Map => loc(Loc) |-> intern(E) loc(Loc +Rat 1) |-> intern([EL * E']))
       <_/store>
       <nextLoc> Loc => Loc +Rat 2 </nextLoc> [structural]

endkm

kmod EXTERN is including SKEME-SEMANTICS
  op extern  : K Map -> Exp
  op externS : String Map Map Int -> String
  op externV : List{Exp} Map Map Int -> Exp 
  op _+StringK_ : K String -> String

  eq Str1:String +StringK Str2:String = Str1 +String Str2

 
  --- externing for literals    
  rule extern(vT, M:Map)           => #t            [structural]
  rule extern(vF, M)               => #f            [structural]
  rule extern(vUnspec, M)          => #unspecified  [structural]
  rule extern(vn(ID:Id), M)        => ID            [structural]
  rule extern(vf(F:Float), M)      => F             [structural]
  rule extern(vr(R:Rat), M)        => R             [structural]
  rule extern(vc(C), M)            => #\C:Char      [structural]
  rule extern(vNil, M)             => []            [structural]
  rule extern(string(.Map # 0), M) => ""            [structural]
  rule extern(vec(.Map # 0), M)    => #[]           [structural]

  --- externing Closures
  rule extern(closure(EL1:List{Exp}, EL2:List{Exp}, CEnv:Map), M)        
    => #procedure(closure(EL1, EL2, CEnv)) [structural]

  rule extern(varClosure(EL1:List{Exp}, E:Exp, EL2:List{Exp}, CEnv:Map), M)        
    => #procedure(varClosure(EL1, E, EL2, CEnv)) [structural]

  --- externing Continuation
  rule extern(continuation(K:K, CEnv:Map), M)        
    => #continuation(continuation(K, CEnv)) [structural]

  --- externing for Strings
  rule extern(string( M:Map # Len:NzInt ), Store:Map)
    => externS("", M, Store, (-Int 1) +Int Len) [structural] 

  rule externS(Str:String, M, Store, 0)  
    => Store(M(0)) +StringK Str [structural]

  rule externS(Str:String, M, Store, Nz:NzInt) 
    => externS(Store(M(Nz)) +StringK Str, M, Store, (-Int 1) +Int Nz) [structural]

  --- externing for Vectors
  rule extern(vec( M:Map # Len:NzInt ), Store:Map)
    => externV(.List{Exp}, M, Store, (-Int 1) +Int Len) [structural] 

  rule externV(EL:List{Exp}, M, Store, 0)  
    => #[extern(Store(M(0)), Store) EL] [structural]

  rule externV(EL, M, Store, Nz:NzInt) 
    => externV(extern(Store(M(Nz)), Store) EL, M, Store, (-Int 1) +Int Nz) [structural]

  --- externing for Lists
  rule extern(cons(loc(R1:Rat) * loc(R2:Rat)), M)
    => [extern(M(loc(R1)), M) * extern(M(loc(R2)), M)] [structural]
endkm

--- I don't like how I have to essentially rewrite intern for all literals here,
--- but we can't match on sort in K.  Is there a better way to do this?
--- I'd like to say any Literal on the top of the K rewrites to intern of that Literal
kmod LITERAL-SEMANTICS is including SKEME-SEMANTICS

  rule <k> #t => vT                   <_/k> [structural]
  rule <k> #f => vF                   <_/k> [structural]
  rule <k> #unspecified => vUnspec    <_/k> [structural]
  rule <k> F:Float => vf(F)           <_/k> [structural]
  rule <k> R:Rat => vr(R)             <_/k> [structural]
  rule <k> #\C:Char  => vc(C)         <_/k> [structural]
  rule <k> []        => vNil          <_/k> [structural]
  rule <k> #[]       => vec(.Map # 0) <_/k> [structural]
  rule <k> [* E:Exp] => E             <_/k> [structural]
endkm

kmod STRING-SEMANTICS is including INTERN
  rule <k> Str:String => intern(Str) <_/k>  
endkm

kmod VECTOR-SEMANTICS is including INTERN
  rule <k> #[EL:List{Exp}] => intern(#[EL]) <_/k>  
endkm

kmod ID-SEMANTICS is including SKEME-SEMANTICS
  rule <k> ID:Id => Store(Env(ID)) <_/k> 
       <env> Env:Map </env>
       <store> Store:Map </store>
  if $hasMapping(Env, ID)
  
  rule <k> ID:Id => Store(GEnv(ID)) <_/k> 
       <env> Env:Map </env>
       <globalEnv> GEnv:Map </globalEnv>
       <store> Store:Map </store>
  if notBool($hasMapping(Env, ID))
endkm

kmod DEFINE-SEMANTICS is including SKEME-SEMANTICS
  op def : Exp Exp -> K [strict(2)]

  rule <k> [define ID:Id E:Exp] => def(ID,E) <_/k> [structural]
  
  rule <k> def(ID:Id, I:Internal) => vUnspec  <_/k> 
       <globalEnv_> .Map => ID |-> loc(N:Rat) </globalEnv> 
       <store_>     .Map => loc(N) |-> I      </store>
       <nextLoc>     N => N +Rat 1            </nextLoc>   
endkm

kmod SET!-SEMANTICS is including SKEME-SEMANTICS
  op set : Exp Exp -> K [strict(2)]

  rule <k> [set! ID:Id E:Exp] => set(ID,E) <_/k> [structural]

  ---check local env first  
  ---if it exists in local set the local copy
  rule <k> set(ID:Id, I:Internal) => vUnspec  <_/k> 
       <env_>        ID |-> loc(N:Rat)        </env> 
       <store_>      loc(N) |-> (_ => I)      </store>

  ---if it does not exist in lcoal we assume (for now)
  ---that it must exist in global.  Set that copy
  rule <k> set(ID:Id, I:Internal) => vUnspec  <_/k> 
       <env_>        Env:Map                  </env>
       <globalEnv_>  ID |-> loc(N:Rat)        </globalEnv> 
       <store_>      loc(N) |-> (_ => I)      </store>
    if notBool($hasMapping(Env, ID))
endkm

kmod QUOTE-SEMANTICS is including INTERN
  rule <k> [quote E:Exp] => intern(E) <_/k>
endkm 

kmod IF-SEMANTICS is including SKEME-SEMANTICS
  op ite : Exp Exp Exp -> K [strict(1)]
     
  rule <k> [oif E1:Exp E2:Exp E3:Exp] => ite(E1, E2, E3)  <_/k> [structural]
  rule ite(vT, E1, E2) => E1
  rule ite(vF, E1, E2) => E2
endkm

kmod BEGIN-SEMANTICS is including SKEME-SEMANTICS
  op beg : List{Exp} -> K

  rule <k> [begin E:Exp EL:List{Exp}] => E ~> beg(EL) <_/k> [structural]
  rule I:Internal ~> beg(E:Exp EL:List{Exp}) 
    => E ~> beg(EL)
  rule I:Internal ~> beg(.List{Exp})
    => I 
endkm

kmod LAMBDA-SEMANTICS is including SKEME-SEMANTICS
  rule <k> [lambda [EL1:List{Exp}] EL2:List{Exp}] => closure(EL1, EL2, Env:Map) <_/k>
       <env> Env </env>
  
  --- this rule is unfortunately necessary because of [.List{Exp}] = [] macro
  --- though in all other respects that macro makes life easier
  rule <k> [lambda [] EL2:List{Exp}] => closure(.List{Exp}, EL2, Env:Map) <_/k>
       <env> Env </env>

  rule <k> [lambda [EL:List{Exp} * E:Exp] EL':List{Exp}] => varClosure(EL, E, EL', Env:Map) <_/k>  
       <env> Env </env>
  
  --- this rule is unfortunately necessary because of [.List{Exp} * Exp] = [* Exp] macro
  --- though in all other respects that macro makes life easier
  rule <k> [lambda [* E:Exp] EL':List{Exp}] => varClosure(.List{Exp}, E, EL', Env:Map) <_/k>  
       <env> Env </env>
endkm

kmod APPLY-SEMANTICS is including SKEME-SEMANTICS
  op apply : List{Exp} -> K [strict] 
  
  rule <k> [E:Exp EL:List{Exp}] => apply(E EL) <_/k> <keywords> S:Set </keywords>
    if notBool(SetItem(E) in S) [structural] 
endkm

kmod CLOSURE-SEMANTICS is including APPLY-SEMANTICS
  rule <k> apply(closure(EL1:List{Exp}, EL2:List{Exp}, CEnv:Map) IL:List{Internal})
           => bind(EL1, IL) ~> [begin EL2] ~> restore(Env:Map) <_/k>
       <env> Env => CEnv </env>
    
  rule <k> apply(varClosure(EL1:List{Exp}, E:Exp, EL2:List{Exp}, CEnv:Map) IL:List{Internal})
           => varBind(EL1, E, IL) ~> [begin EL2] ~> restore(Env:Map) <_/k>
       <env> Env => CEnv </env>
endkm

kmod CALL-CC-SEMANTICS is including APPLY-SEMANTICS
  rule <k>   apply(bCallCC I:Internal) ~> K:K => apply(I:Internal continuation(K, Env:Map)) ~> K </k>
       <env> Env </env>

  rule <k> apply(continuation(K':K, Env':Map) I:Internal) ~> K:K
           => I ~> K' 
       </k>
       <env> _ => Env' </env>
endkm

kmod EVAL-SEMANTICS is including APPLY-SEMANTICS + EXTERN
     rule <k> apply(bEval I:Internal) => extern(I, M:Map) <_/k> <store> M </store> 
endkm

kmod DISPLAY-SEMANTICS is including APPLY-SEMANTICS + EXTERN

     rule <k> apply(bDisplay I:Internal) => vUnspec <_/k> 
          <output_> .List => ListItem(extern(I, Store:Map)) </output> 
          <store> Store </store> 
endkm

kmod EQUALITY-SEMANTICS is including APPLY-SEMANTICS
  rule apply(b= I1:Internal I2:Internal) => #t if I1 ==Bool I2
  rule apply(b= I1:Internal I2:Internal) => #f if I1 =/=Bool I2
endkm

kmod ARITHMETIC-SEMANTICS is including APPLY-SEMANTICS
  op plus : List{Internal} -> K
  op plusf : List{Internal} -> K

  rule apply(b+ IL:List{Internal}) => plus(vr(0) IL) [structural]
  rule plus(vr(R1:Rat) vr(R2:Rat) IL:List{Internal})
    => plus(vr(R1 +Rat R2) IL)
  rule plus(vr(R1:Rat) vf(F2:Float) IL:List{Internal})
    => plusf(vf(Rat2Float(R1) +Float F2) IL)
  rule plus(vr(R1:Rat))
    => vr(R1) 
  rule plusf(vf(F1:Float) vr(R2:Rat) IL:List{Internal})
    => plusf(vf(F1 +Float Rat2Float(R2)) IL)
  rule plusf(vf(F1:Float) vf(F2:Float) IL:List{Internal})
    => plusf(vf(F1 +Float F2) IL)
  rule plusf(vf(F1:Float))
    => vf(F1) [structural]

  op times : List{Internal} -> K
  op timesf : List{Internal} -> K

  rule apply(b* IL:List{Internal}) => times(vr(1) IL) [structural]
  rule times(vr(R1:Rat) vr(R2:Rat) IL:List{Internal})
    => times(vr(R1 *Rat R2) IL)
  rule times(vr(R1:Rat) vf(F2:Float) IL:List{Internal})
    => timesf(vf(Rat2Float(R1) *Float F2) IL)
  rule times(vr(R1:Rat))
    => vr(R1) 
  rule timesf(vf(F1:Float) vr(R2:Rat) IL:List{Internal})
    => timesf(vf(F1 *Float Rat2Float(R2)) IL)
  rule timesf(vf(F1:Float) vf(F2:Float) IL:List{Internal})
    => timesf(vf(F1 *Float F2) IL)
  rule timesf(vf(F1:Float))
    => vf(F1) [structural]

  --- applying - to no arguments should
  --- provoke an error, add when we do
  --- error messages

  op sub : List{Internal} -> K
  op subf : List{Internal} -> K

  rule apply(b- vr(R1:Rat)) => vr(-Rat R1) [structural]
  rule apply(b- vf(F1:Float)) => vf(-Float F1) [structural] 
  rule apply(b- vr(R1:Rat) IL:List{Internal}) => sub(vr(R1) IL) if IL =/=Bool .List{Internal} [structural] 
  rule apply(b- vf(F1:Float) IL:List{Internal}) => subf(vf(F1) IL) if IL =/=Bool .List{Internal} [structural]

  rule sub(vr(R1:Rat) vr(R2:Rat) IL:List{Internal})
    => sub(vr(R1 +Rat (-Rat R2)) IL)
  rule sub(vr(R1:Rat) vf(F2:Float) IL:List{Internal})
    => subf(vf(Rat2Float(R1) +Float (-Float F2)) IL)
  rule sub(vr(R1:Rat))
    => vr(R1) 
  rule subf(vf(F1:Float) vr(R2:Rat) IL:List{Internal})
    => subf(vf(F1 +Float (-Float Rat2Float(R2))) IL)
  rule subf(vf(F1:Float) vf(F2:Float) IL:List{Internal})
    => subf(vf(F1 +Float (-Float F2)) IL)
  rule subf(vf(F1:Float))
    => vf(F1) [structural]

  op div : List{Internal} -> K
  op divf : List{Internal} -> K

  --- applying / to no arguments should
  --- provoke an error, add when we do
  --- error messages

  rule apply(b/ vr(NzR1:NzRat)) => vr((1 /Rat NzR1)) [structural]
  rule apply(b/ vf(F1:Float)) => vf(1.0 /Float F1) [structural] 
  rule apply(b/ vr(NzR1:NzRat) IL:List{Internal}) => div(vr(NzR1) IL) if IL =/=Bool .List{Internal} [structural] 
  rule apply(b/ vf(F1:Float) IL:List{Internal}) => divf(vf(F1) IL) if IL =/=Bool .List{Internal} [structural]

  rule div(vr(R1:Rat) vr(NzR2:NzRat) IL:List{Internal})
    => div(vr(R1 /Rat NzR2) IL)
  rule div(vr(R1:Rat) vf(F2:Float) IL:List{Internal})
    => divf(vf(Rat2Float(R1) /Float F2) IL)
  rule div(vr(R1:Rat))
    => vr(R1) 
  rule divf(vf(F1:Float) vr(NzR2:NzRat) IL:List{Internal})
    => divf(vf(F1 /Float Rat2Float(NzR2)) IL)
  rule divf(vf(F1:Float) vf(F2:Float) IL:List{Internal})
    => divf(vf(F1 /Float F2) IL)
  rule divf(vf(F1:Float))
    => vf(F1) [structural]
endkm

kmod LIST-OPS is including APPLY-SEMANTICS

  rule <k> apply(bCons I1:Internal I2:Internal) => cons(loc(Loc:Rat) * loc(Loc +Rat 1)) <_/k>
       <store_> .Map => loc(Loc) |-> I1 loc(Loc +Rat 1) |-> I2 </store>
       <nextLoc> Loc => Loc +Rat 2 </nextLoc> 

  rule <k> apply(bCar cons(L1:K * L2:K)) => Store:Map(L1) <_/k> 
       <store> Store </store>
  rule <k> apply(bCdr cons(L1:K * L2:K)) => Store:Map(L2) <_/k> 
       <store> Store </store>

  rule <k> apply(bSetCar cons(L1:K * L2:K) I:Internal) => vUnspec <_/k> 
       <store_> L1 |-> (_ => I) </store>
  rule <k> apply(bSetCdr cons(L1:K * L2:K) I:Internal) => vUnspec <_/k> 
       <store_> L2 |-> (_ => I) </store>
endkm

kmod SKEME is including 
    LITERAL-SEMANTICS + STRING-SEMANTICS + VECTOR-SEMANTICS 
  + ID-SEMANTICS + DEFINE-SEMANTICS + SET!-SEMANTICS + QUOTE-SEMANTICS + IF-SEMANTICS + BEGIN-SEMANTICS
  + SKEME-PROGRAMS + LAMBDA-SEMANTICS + CLOSURE-SEMANTICS + CALL-CC-SEMANTICS 
  + APPLY-SEMANTICS + EVAL-SEMANTICS + DISPLAY-SEMANTICS
  + EQUALITY-SEMANTICS + ARITHMETIC-SEMANTICS
  + LIST-OPS
  
  syntax Bag ::= run( List{K} ) | out( List ) 

     op KLtoL : List{K} -> List 
     eq KLtoL((K:K ,, KL:List{K})) = ListItem(K) KLtoL(KL)  
     eq KLtoL(.List{K}) = .List

  ---intial run macro, this starts interpretation
  macro run(KL:List{K}) = <T_> <program> KLtoL(KL) </program> <_/T>
  
  --- if all that remains is a value, dissolve it
  rule <k> KR:KResult => .K </k> 

  --- if the k cell is empty, we take the first expression in the program and put it
  --- in the k cell
  rule <k> .K => K </k> 
       <program> ListItem(K) => .List <_/program> [structural] 
  
  --- end condition
  rule <T_> <k> .K </k> 
            <program> .List </program> 
            <output> L:List </output> 
       <_/T> => out(L) [structural] 
 endkm

