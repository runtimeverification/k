require ocl-syntax
require meta-model
require values
require substitution
kmod OCL-SEMANTICS is including OCL-SYNTAX + META-MODEL + VALUES  +  SUBSTITUTION 


syntax Exp ::= Val
// contents of K cell : Expressions
syntax K ::= Exp

//SEMANTICS
//identifiers evaluate to themselves: no rule needed

// ARITHMETICAL EXPRESSIONS
// Note : most mixed scalar/nonscalar combinations are handled in VALUES module
// in a generic, operator-independent way
rule <k> A1:Int + A2:Int => A1 +Int A2  <_/k> [structural]
rule  <k> A1 * A2 => A1 *Int A2 <_/k> [structural]
rule  <k>A1 / A2 => A1 /Int A2 <_/k> if notBool (A2 ==Int 0)  [structural]
rule  <k> (- A1) => -Int A1 <_/k>  [structural]

rule <k> (val(B:Bag) .size()) => card(B) <_/k> [structural]
// some mixed scalar/nonscalar non handled in VALUES (not "generic" enough)
rule <k> (I:Int .size()) => 1 <_/k> [structural]
rule <k> (bbb:Bool .size()) => 1  <_/k> [structural]
rule <k> (Str:String .size()) => 1  <_/k> [structural]

// BOOLEAN
rule <k> A1 < A2 => A1 <Int A2 <_/k>   [structural]
rule <k>  A1 <= A2 => A1 <=Int A2 <_/k>  [structural]
rule <k>  A1 > A2 => A1 >Int A2 <_/k>  [structural]
rule <k>  A1 >= A2 => A1 >=Int A2 <_/k>   [structural]
// because and etc are strict only in first arg
rule <k>  true and E:Exp => E   <_/k> [structural]
rule <k>  false and E => false   <_/k> [structural]

rule <k>  true or E => true  <_/k>  [structural]
rule <k>  false or E => E  <_/k>   [structural]

rule <k>  true implies E => E  <_/k>   [structural]
rule <k>  false implies E => true  <_/k>  [structural]

rule <k>  not B1:Bool => notBool B1  <_/k>  [structural]


// equality,  for all types

rule <k> (Id1:Id = Id2:Id) => Id1 ==Bool Id2 <_/k> [structural]
rule  <k> A1 = A2 => A1 ==Int A2  <_/k>  [structural]
rule  <k> (Str1 = Str2) => Str1 ==Bool Str2  <_/k>  [structural]
rule   <k> (B1 = B2:Bool) =>  B1 ==Bool B2  <_/k>  [structural]
// for non-scalar types, equality = equality of bags
// this relies on the invariant that there is at most
// one pair (instance name, class name) per model.
rule <k> (val(C1) = val(C2)) => C1 ==Bool C2  <_/k>[structural] 


//includes, excludes
rule <k> val(C1:Bag) includes val(C2:Bag) => subset(C2,C1)  <_/k>  [structural]

rule <k> val(C1:Bag) excludes val(.Bag) => true  <_/k> [structural]

rule   <k> val(Bg:BagItem C1:Bag) excludes val(Bg:BagItem C2:Bag) => false <_/k>  [structural]
rule  <k> val(C1:Bag) excludes val(Bg':BagItem C2:Bag) => 
val(C1:Bag) excludes val(C2:Bag) <_/k> if notBool(Bg' in C1)  [structural]

// isEmpty
rule <k> isEmpty(val(.Bag)) => true <_/k> [structural]
rule  <k>isEmpty(val(BagIt:BagItem _)) => false <_/k> [structural]
// no need to define isEmpty() for scalars (it should be an error)



//forAll
// overloading the substitution operator to  expressions
syntax Exp ::=  Exp [ K / Id ] [ditto]
// base case
rule <k> val(.Bag) ->forAll(_| _) => true <_/k> [structural]



// inductive step
rule <k>
val(( BI:BagItem B:Bag)) ->forAll( Var:Id | BEXP:Exp ) => 
if 
BEXP[open(BI)/Var] 
then val(B) ->forAll( Var | BEXP)
else false
endif 
<_/k> 
[structural]

// the value replacing the variable need to be "opened"
syntax K ::= open ( BagItem )
rule open(BagItem(kv:K)) => kv [structural]

//exists 
rule  <k> val(.Bag) ->exists(_| _) => false <_/k> [structural]
rule <k>
val(( BI:BagItem B:Bag)) ->exists( Var:Id | BEXP:Exp ) => 
if  BEXP[open(BI)/Var] 
then true 
else val(B) ->exists( Var | BEXP)
endif 
<_/k> 
[structural]

//STRINGS
rule <k>  Str1:String ++ Str2:String => Str1 +String Str2 <_/k> [structural]


// COLLECTIONS
// rule for empty
rule <k> empty => val(.Bag) <_/k> [structural]

// rules allInstances(Class)
rule <k> allInstances(Cls:Id) => val(collectInstanceNames(Cls, INST:Bag)) <_/k>  
       //NB one model only!
      <models>
         <model> <modelName> _:Id </modelName> // 
            INST
         </model>
     </models>
 [structural] 

//collectInstances function: collects instances of class Cls
syntax Bag ::= collectInstanceNames ( Id , Bag ) 
rule collectInstanceNames(Cls, .Bag) => .Bag [structural]

rule collectInstanceNames(Cls, 
                        (<instance> 
                             <instName> INAME:Id </instName> 
                             <ofClass> Cls </ofClass>
                             <attributes> ATTR:Map </attributes>
                         </instance> 
                        REST:Bag
                       )
                     )
                      =>    BagItem(INAME : Cls)
                      collectInstanceNames(Cls, REST) [structural]

rule collectInstanceNames(Cls, 
                        (<instance> 
                             <instName> INAME </instName> 
                             <ofClass> Cls':Id </ofClass>
                             <attributes> ATTR </attributes>
                         </instance> REST:Bag))
                        =>  collectInstanceNames(Cls, REST)
                        if notBool (Cls ==Bool Cls') [structural]

// ":"
rule <k> INAME : Cls => val(BagItem(INAME : Cls)) <_/k> [structural]


// rule for CExp # Id [strict] 
// CARE all elements in CExp are assumed to have the attribute Id!!!
// may write a typechecker in the future to check that

syntax K ::= * Nat
kvar N N' : Nat 
syntax K ::= [  K , K ]

// initialisation : head of computation replaced by *N
rule <k>  val(REMAINING:Bag) # AT:Id
           =>
           * N
 <_/k>
// [expression, index to its value]  stored in mem at index N, its value at N+1
 <mem_> . => (N |->  [ val(REMAINING) # AT:Id  , N +Nat 1]
              N +Nat 1 |-> val(.Bag))
 <_/mem>
 <nextLoc> N => N +Nat 2 </nextLoc> // N updated


// loop step : while *N is head of computation
 rule <k> * N <_/k>
// perform one step - reduce expression at N, store intermediary result in N+1
 <mem_> N |->  [(val(BagItem(INAME : Cls) REMAINING:Bag) # AT:Id => val(REMAINING) # AT), N']
             N' |-> val ( _ (.Bag => B))
 <_/mem>
// find INSNAME, Cls instance in model
 <models>
 <model_>
 <instance>
 <instName> INAME </instName>
 <ofClass> Cls </ofClass>
//use its attribute values at AT
 <attributes_> AT |-> typedElt(val(B:Bag),T:Id) <_/attributes>
 </instance>
 <_/model>
 </models>
      [structural]


// loop step 2nd rule : while *N is head of computation
 rule <k> * N <_/k>
// perform one step - reduce expression at N, store intermediary result in N+1
 <mem_> N |->  [(val(BagItem(INAME : Cls) REMAINING:Bag) # AT:Id => val(REMAINING) # AT), N']
             N' |-> val ( _ (.Bag => B))
 <_/mem>
// find INSNAME instance in model, find its class in metamodel as a superclass of Cls
<metamodel_>
 <classes_>
  <class_>
    <className> Cls':Id</className>
    <extends> BagItem(Cls:Id) _ </extends>
  <_/class>
 <_/classes>
<_/metamodel>
 <models>
 <model_>
 <instance>
 <instName> INAME </instName>
 <ofClass> Cls' </ofClass>
//use its attribute values at AT
 <attributes_> AT |-> typedElt(val(B:Bag),T:Id) <_/attributes>
 </instance>
 <_/model>
 </models>
if notBool(Cls' ==Bool Cls)
      [structural]


//last step : replace head of computation by result, empty locations in memory
 rule <k>  * N => val(B) <_/k>
 <mem_> ((N |-> [(val(.Bag) # AT), N'])
        (N' |-> val(B))) => .
 <_/mem>
 [structural]



//union: also with scalar types
rule <k> val(C1) union val(C2)   => val(C1 C2) <_/k> [structural]
// this case not handled by generic rule for mixing scalar/nonscalar due to circularity
rule <k> Val1:Val union Val2:Val   => val(BagItem(Val1) BagItem(Val2)) <_/k> 
// CARE !! enum types also scalar
if isScalar((Val1)) andBool isScalar((Val2))
[structural]

//CARE! if other binary ops to be added (difference etc) a rule similar to the above 
// one must be added 

//collect: by analogy with forAll, exists
rule <k> val(.Bag) ->collect(_|_) => val(.Bag)  <_/k> [structural]

rule <k>
 val(( BI:BagItem B:Bag)) ->collect( Var:Id | CEXP:Exp ) =>
   (val(B) ->collect( Var | CEXP))  union CEXP[open(BI)/Var]
<_/k>
 [structural]


//select : uses the same generic approach for handling intermediary results as #AT
rule <k>  val(B) ->select( Var| BEXP:Exp )
           =>
           * N
 <_/k>
 <mem_> . => (N |-> [val(B)->select( Var| BEXP:Exp)  , N +Nat 1]
              N +Nat 1 |-> val(.Bag))
 <_/mem>
 <nextLoc> N => N +Nat 2 </nextLoc>

 rule <k> * N <_/k>
 <mem_> N |->  [val(BI B)->select( Var| BEXP:Exp) => (val(B) ->select( Var| BEXP:Exp)), N']
        N'|->  (EXP:Exp => EXP union (if BEXP[open(BI)/Var] then val(BI) else val(.Bag) endif))
 <_/mem>
      [structural]



 rule <k>  * N => EXP <_/k>
 <mem_> ((N |-> [val(.Bag)->select(Var| BEXP:Exp), N'])
        (N' |-> EXP)) => .
 <_/mem>
 [structural]



// let : just substitution
rule <k> let  X:Id =  CEXP1 in CEXP2  endlet => CEXP2[CEXP1/X] <_/k> [structural]

// if
rule <k> if true then CEXP1:Exp else CEXP2:Exp endif => CEXP1 <_/k> [structural]
rule <k> if false then CEXP1 else CEXP2 endif => CEXP2 <_/k> [structural]

// condition can be a non-scalar (non handled by generic rules in VALUES)
rule <k> if val(BagItem(true)) then CEXP1:Exp else CEXP2:Exp endif => CEXP1 <_/k> [structural]
rule <k> if val(BagItem(false)) then CEXP1 else CEXP2 endif => CEXP2 <_/k> [structural]
/*
//oclType : computes the type of an already evaluated expression
// for arithmetical, boolean, string expressions: just returns their basic type
// for collections: computes the lub (least upper bound) of types of elements inside

// arithmetical, boolean, string
rule <k> oclType(A1) => int <_/k>[structural]
rule <k> oclType(B1) => bool  <_/k> [structural]
rule <k> oclType(Str1) => string  <_/k> [structural]

// collections
// the lattice is : top - everything (flat)
// will change in the future when we add inheritance

rule <k>  oclType(val(BagItem (A1))) => int  <_/k>  [structural]
rule <k>  oclType(val(BagItem (B1))) => bool  <_/k> [structural]
rule <k>  oclType(val(BagItem (Str1))) => string  <_/k> [structural]

// collections of int, bool, string
rule  <k> oclType(val(BagItem (A1) BagItem(A2) B:Bag)) =>
      oclType(val(BagItem(A2) B:Bag))  <_/k>  [structural]
rule   <k> oclType(val(BagItem (B1) BagItem(B2) B:Bag)) =>
      oclType(val(BagItem(B2) B:Bag))  <_/k>  [structural]
rule  <k>  oclType(val(BagItem (Str1) BagItem(Str2) B:Bag)) =>
      oclType(val(BagItem(Str2) B:Bag))  <_/k>  [structural]

//mixtures : return top
rule <k>  oclType(val(BagItem (A1) BagItem(B1) _)) => top  <_/k> [structural]
rule <k>  oclType(val(BagItem (A1) BagItem(Str1) _)) => top  <_/k> [structural]
rule <k>  oclType(val(BagItem (A1) BagItem(_ : _) _)) => top  <_/k> [structural]
rule <k>  oclType(val(BagItem (B1) BagItem(Str1) _)) => top  <_/k> [structural]
rule <k>  oclType(val(BagItem (B1) BagItem(_ : _) _)) => top   <_/k>[structural]
rule <k>  oclType(val(BagItem (Str1) BagItem(_ : _) _)) => top  <_/k> [structural]

// isntances
rule oclType(val(BagItem (_ : Cls))) => Cls  [structural]
rule oclType (val(BagItem (_: Cls) BagItem (Ins2:Id : Cls)  B:Bag))
 => oclType (val(BagItem (Ins2 : Cls)  B:Bag))  [structural]
// for now, the lub of two distinct classes is just "top"
// will change in the future when we add inheritance
rule oclType (val(BagItem (_ : Cls) BagItem (_ : Cls':Id)  _))
=> top if notBool (Cls ==Bool Cls')  [structural]
// and finally, empty
rule oclType(val(.Bag)) => top [structural]
 */
endkm

