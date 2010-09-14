in ../../../k-prelude

kmod SKEME-SYNTAX is including PL-INT + PL-RAT + PL-FLOAT + PL-ID + PL-STRING 

  syntax Literal ::=  #t  | #f | #unspecified 
                    | []  | #[]
                    | Int | Float | Rat | #\ Char 

  syntax Exp ::= Literal 
               | Id | String  
               | [ List{Exp} ] | #[ List{Exp} ] | [ List{Exp} * Exp ] | [* Exp ]  
               | `! Exp

  syntax List{Exp} ::= Exp | .List{Exp} | List{Exp}  List{Exp} [assoc id: .List{Exp} strict hybrid] 
  
  op length : List{Exp} -> Int
  eq length(E:Exp EL:List{Exp}) = 1 +Int length(EL)
  eq length(.List{Exp}) = 0 

  syntax Program ::= program(List{Exp}) 

  syntax Id ::= eval | display | set-car! | set-cdr! | o= | o+ | o- | o* | o/
              | call-with-current-continuation | call/cc | car | cdr 
              | if | quote | begin

  macro [ .List{Exp} ] = [] 
  macro [ .List{Exp} * E:Exp ] = [* E] 
  macro #[ .List{Exp} ] = #[]
  macro [EL:List{Exp} * []] = [EL:List{Exp}] 
  macro [EL:List{Exp} * [EL':List{Exp}]] = [EL:List{Exp} EL':List{Exp}] 
  macro [EL:List{Exp} * [EL':List{Exp} * E:Exp]] = [EL:List{Exp} EL':List{Exp} * E:Exp] 
  macro ! E:Exp = [quote E]
endkm

kmod SKEME-INTERNAL is including K + SKEME-SYNTAX

  syntax Closure  ::=   closure(List{Id}, List{Exp}, Map)
                      | varClosure(List{Id{, Id, List{Exp}, Map)

  syntax Continuation ::= continuation(K, Map)

  syntax Internal ::=   vT | vF | vUnspec | vNil 
                      | vi( Int ) | vf( Float ) | vr( Rat ) | vc( Char ) | vn( Id )                                           
                      | cons( K * K ) | vec( Map # Int ) | string( Map # Int ) | Builtin 
  
  syntax Builtin ::=   bEval | bDisplay | bSetCar | bSetCdr | bEqual | b+ | b- | b* | b/ 
                     | bCallCC | bCar | bCdr

  syntax List{Id} ::= Id | .List{Id} | List{Id} , List{Id} [assoc id: .List{Id}]
  
  syntax List{Internal} ::= Internal | .List{Internal} | List{Internal} :: List{Internal} [assoc id: .List{Internal}]
 
  syntax Literal ::= #procedure(Closure) | #continuation(Continuation) | #builtin(Builtin)   
  
  syntax Exp ::= Internal
  syntax List{Exp} ::= List{Internal}

endkm

kmod SKEME-PROGRAMS is including SKEME-SYNTAX
  syntax List{Exp} ::= bar | foo | baz | chaz | kraz | apply | apply2 | id-test 

  ---macro foo = [eval ![1 * 2]]
  macro foo = #[]
---  macro bar = []
  macro bar = [if #t "true" "false"]
  macro baz = #[#[#[3]] "true"]
  macro chaz = [eval ![1 * [2]]]
  macro kraz = ![#[42 [43]] "44"]
  macro apply = [1 2 3 4]
  macro apply2 = [1]
  macro id-test = eval
endkm

kmod SKEME-SEMANTICS is including SKEME-INTERNAL


  syntax K ::= Program | Exp | Char | String 
  syntax KResult ::= Internal

  op loc : K -> K

  configuration <T> <k>.K</k> 
                    <program>   .List </program>
                    <globalEnv> 
                       eval                           |-> loc(0)                         
                       display                        |-> loc(1)  
                       set-car!                       |-> loc(2) 
                       set-cdr!                       |-> loc(3) 
                       o=                             |-> loc(4) 
                       o+                             |-> loc(5) 
                       o-                             |-> loc(6)  
                       o*                             |-> loc(7)  
                       o/                             |-> loc(8)  
                       call-with-current-continuation |-> loc(9)   
                       call/cc                        |-> loc(9)   
                       car                            |-> loc(10) 
                       cdr                            |-> loc(11) 
                    </globalEnv> 
                    <env> .Map </env> 
                    <store>     
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
                    </store> 
                    <nextLoc> 12 </nextLoc> 
                    <output> .List </output>
                    <keywords> SetItem(if) SetItem(quote) SetItem(begin) </keywords>
               </T>
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
  rule intern(I:Int)        => vi(I)         [structural]
  rule intern(F:Float)      => vf(F)         [structural]
  rule intern(R:Rat)        => vr(R)         [structural]
  rule intern(#\C:Char)     => vc(C)         [structural]
  rule intern([])           => vNil          [structural]
  rule intern(#[])          => vec(.Map # 0) [structural]
  rule intern([* E:Exp])    => intern(E)     [structural]

  --- interning String
  rule intern( Str:String ) => internS(string(.Map # lengthString(Str)), Str, 0) [structural]  
  
  --- unfortunately we need two versions of this because my 'if' ID confuses things between whether
  --- or not this should be a conditional rule or if 'if' is the ID.  The only way to fix this is
  --- to mention cells explicitly... or perhaps rename 'if'
  --- leaving out of k level v. store level because I want a better way to do this
  rule <k_> internS(KR:KResult, Str, _) => KR <_/k>
    if lengthString(Str) ==Bool 0 [structural]

  rule <store> loc(Loc:Rat) |-> (internS(KR:KResult, Str, _) => KR) <_/store>
    if lengthString(Str) ==Bool 0 [structural]

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
  rule extern(vi(I:Int), M)        => I             [structural]
  rule extern(vf(F:Float), M)      => F             [structural]
  rule extern(vr(R:Rat), M)        => R             [structural]
  rule extern(vc(C), M)            => #\C:Char      [structural]
  rule extern(vNil, M)             => []            [structural]
  rule extern(string(.Map # 0), M) => ""            [structural]
  rule extern(vec(.Map # 0), M)    => #[]           [structural]

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
kmod LITERAL-SEMANTICS is including INTERN

  rule <k> #t => vT                   <_/k> [structural]
  rule <k> #f => vF                   <_/k> [structural]
  rule <k> #unspecified => vUnspec    <_/k> [structural]
  rule <k> I:Int => vi(I)             <_/k> [structural]
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

kmod QUOTE-SEMANTICS is including INTERN
  rule <k> [quote E:Exp] => intern(E) <_/k>
endkm 

kmod IF-SEMANTICS is including SKEME-SEMANTICS
  op ite : K K K -> K [strict(1)]
     
  rule <k> [if E1:Exp E2:Exp E3:Exp] => ite(E1, E2, E3)  <_/k> [structural]
  rule ite(vT, E1, E2) => E1
  rule ite(vF, E1, E2) => E2
endkm

kmod APPLY-SEMANTICS is including SKEME-SEMANTICS
  op apply : List{K} -> K 

  context apply((? ,, `[HOLE`]:K ,, ?))

  rule <k> [E:Exp EL:List{Exp}] => apply((E ,, getList{K}(EL))) <_/k> <keywords> S:Set </keywords>
    if notBool(SetItem(E) in S) [structural] 
endkm

kmod EVAL-SEMANTICS is including APPLY-SEMANTICS + EXTERN
  --- TEST!!!  eval should be treated as a function!
---  op e : -> K 
---  rule <k> [eval E:Exp] => E ~> e <_/k> 
---  
---  rule <k> (KR:KResult ~> e) => extern(KR, M:Map) <_/k> <store> M </store> 

     rule <k> apply((bEval ,, KR:KResult)) => extern(KR, M:Map) <_/k> <store> M </store> [structural]

     rule <k> apply((vi(1) ,, vi(2))) => vi(1) <_/k> [structural]
endkm

kmod SKEME is including 
    LITERAL-SEMANTICS + STRING-SEMANTICS + VECTOR-SEMANTICS 
  + ID-SEMANTICS + QUOTE-SEMANTICS + IF-SEMANTICS + SKEME-PROGRAMS 
  + APPLY-SEMANTICS + EVAL-SEMANTICS
  
  syntax Bag ::= run( List{K} ) | out( List ) 

     op KLtoL : List{K} -> List 
     eq KLtoL((K:K ,, KL:List{K})) = ListItem(K) KLtoL(KL)  
     eq KLtoL(.List{K}) = .List

  ---intial run macro, this starts interpretation
  macro run(KL:List{K}) = <T_> <program> KLtoL(KL) </program> <_/T>
  
   
  --- silly test
---  rule <k> [3] => .K <_/k> [structural]
---  rule <k> [4] => .K <_/k> [structural]
---  rule <k> [5] => .K <_/k> [structural]


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

