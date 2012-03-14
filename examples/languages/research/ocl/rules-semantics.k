require values.maude
require rules-syntax
require ocl-semantics
require /modules/substitution

module RULES-SEMANTICS 
  imports RULES-SYNTAX + OCL-SEMANTICS

  syntax K ::= #Id 
  syntax #Id ::= "undefined"

  configuration <T>  
			<oclConstraints> .List </oclConstraints>
			<instances> 
			  <instance multiplicity = "*">
				 <instName> undefined </instName>
				 <ofClass> undefined </ofClass>
				 <attributes> .Map </attributes>
			  </instance>
			</instances>
			<k color="green"> .K </k> 
			<trace> .List </trace>
			<result> .List </result> 
			<env> .Map </env>
                </T>


syntax K ::= "restore" "(" Map ")"

rule <k> call ( I:#Id ) => I ~> restore(MM)...</k> 
     <env> MM:Map => .Map </env> [structural]

rule <k> restore(MM:Map) => . ...</k>
     <env> _ => MM ...</env>

syntax K ::= Pgm | Stmt
//1. imperative language for model transformations

// local vars declaration
rule <k> 'var_;_(((I:#Id,Rest:Ids) => Rest) ,, _) ...</k>
     <env> .Map => (I |-> 0) ...</env> [structural]

// local vars declaration
rule <k>  var .Ids ; S:Stmt => S ...</k>  [structural]


// local var assignment
rule <k>  (I:#Id <- V:#MagmaElement) => .K <_/k>
     <env> I |-> (_ => V) ...</env>  [structural]

// local var evaluation
rule <k> I => V ...</k>
     <env>...  I |-> V ...</env>  [structural]

// WARNING: rules only for assignment to singleton Magma
// TODO : typecheck that value is compatible with declared type Tip
rule <k> ((objName:#Id)::(clsName:#Id)) @ fieldName:#Id <- Vv:#Magma => .K ...</k>
     <instances>...
          <instance>
            <instName> objName </instName>
            <ofClass> clsName </ofClass>
			<attributes>...
				fieldName |-> (typedElt(_, (Tip:#Id)) => typedElt(Vv, Tip))
			...</attributes>
          </instance>
     ...</instances> [structural]


// for loop : end
rule <k>  for Iter:#Id <- .Magma { _ } => .K ...</k>  [structural]

// for loop : step
rule  <k>  (for  Iter:#Id <- (Obj:#Object ;Magma Mgm:#Magma) { S })  => 
           S[Obj/Iter] ~> (for Iter <- Mgm { S })       ...</k>  [structural]

// if-then
rule <k> if true  then  { S }  => S ...</k>  [structural]
rule <k> if false then  { S }  => . ...</k>  [structural]

// if-then-else
rule <k> if true then  { S } else { _ } => S ...</k>  [structural]
rule <k> if false then { _ } else { S } => S ...</k>  [structural]

syntax ListItem ::= [ #MagmaElement ]

// print
rule <k> print(V) => .K ...</k> 
     <trace>... .List => [V] </trace>  [structural]

//sequence
rule <k> S1:Stmt ; S2:Stmt => S1 ~> S2 ...</k>  [structural]

//skip
rule <k> skip => .K ...</k>  [structural]





// 2. rules for model transformation

//when
rule   <k> when(true) => .K ...</k>
rule   <k> (when(false) ~> K1:K) => cleanUp  </k>  [structural]


//multiple substitutions
syntax Bag ::= Bag [ Map ]



//update
rule   <k> update(<instances> Rhs:Bag </instances> ) => .K ...</k> 
       <env>  E:Map </env> 
       (<instances> Lhs:Bag => (Rhs[E]) </instances>)  [structural]


syntax Bag ::=  Bag [ K / #Id ]

rule B[ .Map ] => B:Bag [structural]
rule B[ (X:#Id |-> K1:K) E ]  => (B[K1 / X])[E] [structural]


rule (<instances> B:Bag </instances> [K1/X]) =>
     (<instances>  B[K1/X] </instances>) [structural]


rule (.Bag [K1/X]) => .Bag [structural]

rule ((<instName> Nm:#Id </instName> B) [K1/X])
    => <instName> Nm </instName> ( B[K1/X]) [structural]

syntax Map ::= Map [[ K / #Id ]]

rule ((<instance> <attributes> E </attributes> B </instance> B':Bag) [K1/X])
   => (<instance> <attributes> E [[K1/X]] </attributes> B </instance> (B'[K1/X])) [structural]



rule .Map [[K1/X]] => .Map [structural]

rule ((((X1:#Id |-> typedElt(Mgm:#Magma,Typ:#Id))) E) [[K1/X]]) => 
       ((X1 |-> typedElt(Mgm[K1/X],Typ)) (E[[K1/X]])) [structural]


// rule ((BagItem(X) B) [K1/X]) =>  BagItem(K1) (B[K1/X]) [structural]

// rule ((BagItem(X1) B) [K1/X]) =>  BagItem(X1) (B[K1/X]) if (X =/=Bool X1) [structural]

// rule ((BagItem(I1:#Int) B) [K1/X]) =>  BagItem(I1) (B[K1/X]) [structural]

// rule ((BagItem(BB:#Bool) B) [K1/X]) =>  BagItem(BB) (B[K1/X]) [structural]

// rule ((BagItem(SS:#String) B) [K1/X]) =>  BagItem(SS) (B[K1/X]) [structural]

// rule ((BagItem((Ins:#Id):(Cls:#Id)) B) [K1/X]) => BagItem((Ins):(Cls)) (B[K1/X]) [structural]


//using
rule <k> using(P:Pgm) => P ...</k>  [structural]


//do
rule <k> do(P) => P ...</k>  [structural]


//cleanUp
syntax K ::= cleanUp

rule <k> cleanUp => .K ...</k> 
    <env> _ => .Map </env> [structural]


end module
