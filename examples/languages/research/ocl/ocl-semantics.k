require ocl-syntax
require /modules/substitution
require meta-model-interface
require values.maude

module OCL-SEMANTICS is 
  including  META-MODEL-INTERFACE + OCL-SYNTAX + #MAGMA
  including SUBSTITUTION

/*@ \section{Semantics}
 Here we define the \K semantics of the OCL language. For that we need a \K description
 of the metamodel (the interface of this is included in the module \textsf{META-MODEL-INTERFACE},
 a \K implementation of the operations over values (this is given in the module \textsf{VALUES},
 and a configuration.
*/

/*@ \subsection{Configuration}
  Usually OCL is used as a component of other languages. Therefore here we include only that part of
  the configuration that is needed for the evaluation of the OCL expressions.
  This consists of a cell \textsf{instances} which may include zero or more cells \textsf{instance},
  each one of these describing a concrete instance from the current model. The representation of an instance
  consists of its name (= the content of the cell \textsf{instName}), the class name of which instance it is 
  (= the content of the cell \textsf{ofClass}), and the current values of the attributes (= the content of 
  the cell \textsf{attributes}). In addition, we need a cell \textsf{k} for computations.
*/



  configuration 
		<oclConstraints> .List </oclConstraints>
                <instances color="yellow">
                  <instance color="orange" multiplicity = "*">
                    <instName color="blue"> oclUndefined </instName>
                    <ofClass color="purple"> oclUndefined </ofClass>
                    <attributes color="magenta"> .Map </attributes>
                  </instance>
                </instances>
                <k color="green"> .K </k> 
		<env> .Map </env>
		<nextId> 0 </nextId>
		<trace> .List </trace>
		// <result color="brown"> .List</result>
	
/*@ The \textsf{oclUndefined} value is a special identifier. 
  It is not allowed to have a class or instance with this name.
*/

  syntax #Id ::= "oclUndefined" 

/*@ \subsection{Computations}
The values that the various OCL subsexpressions are evaluated to are described 
in the module \textsf{VALUES}. This help us to write the semantic rules using the
OCL syntax instead of ASTs. The syntax of expression is extended with these values.
*/

  syntax KResult ::= #Magma
  syntax Exp ::= #Magma
//  syntax K ::= #Magma
 
/*@
The expressions are evaluated in the computation cell \textsf{k} and therefore they should be 
declared as being of type \textsf{K}:
*/

  syntax K ::= Exp

  // wrapper for Collections when using models
  syntax K ::= typedElt ( #Magma , #Id )
  syntax K ::= typedElt ( K , #Id )

/*@ \subsection{Semantics of Arithmetical Expressions}
 Each arithmetic operator has a corresponding operator over the values. Since all arithmetical 
 operators are declared as being strict in their arguments, only the case when the arguments are
 values must be considered.
 Note that most mixed scalar/nonscalar combinations are handled in the \textsf{VALUES} module
 in a generic, operator-independent way. However, we have to extend the operations over nonscalar types
 over scalar types in order to have a uniform approach.
\textcolor{red}{Maybe we should revise this aspect.}
  \par
 OCL expressions are stored in different places of configurations. In order
 to avoid that evaluation rules  accidentally affect expressions for which evaluation 
 is not needed, we constrain their application only on the top of the cell \textsf{k}'s content.
*/

rule <k> I1:#Int + I2:#Int => I1 +Int I2  ...</k> [:structural:]
rule <k> I1 * I2 => I1 *Int I2 ...</k> [:structural:]
rule <k> I1 / I2 => I1 /Int I2 ...</k> when notBool (I2 ==Int 0) [:structural:]
rule <k> (- I1) => -Int I1 ...</k>  [:structural:]

rule <k> M:#Magma .size() => card ( M ) ...</k> [:structural:]


/*@ \subsection{Semantics of the Boolean Expressions}
It is similar to that of arithmetic expressions. However, it worth to note
 that the values returned by binary Boolean operators (e.g., \textsf{and}, \textsf{or}) are 
 computed using the short circuit evaluation.
*/

rule <k> I1 < I2 => I1 <Int I2 ...</k>   [:structural:]
rule <k> I1 <= I2 => I1 <=Int I2 ...</k>  [:structural:]
rule <k> I1 > I2 => I1 >Int I2 ...</k>  [:structural:]
rule <k> I1 >= I2 => I1 >=Int I2 ...</k>   [:structural:]

// true and 1 = 1 !!!
rule <k> true and E:Exp => E ...</k> [:structural:]
rule <k> false and E => false ...</k> [:structural:]


rule <k>  true or E => true ...</k>  [:structural:]
rule <k>  false or E => E ...</k>   [:structural:]


rule <k>  true implies E => E ...</k>   [:structural:]
rule <k>  false implies E => true ...</k>  [:structural:]


rule <k>  not Bl1:#Bool => notBool Bl1 ...</k>  [:structural:]

/*@ The \textsf{isEmpty} operator is evaluated only for nonscalar (for now, only bags).
 An attempt to evaluate this operator on scalars should produce an error.
*/

rule <k> isEmpty(M:#Magma) => empty (M) ...</k> [:structural:]


rule <k> (Val1:#Magma = Val2:#Magma) => Val1 ==Bool Val2  ...</k> [:structural:] 
// should cover the scalar case as well

/*@ \paragraph{Relations between collections}
*/

rule <k> M1:#Magma includesAll ( M2:#Magma ) => subset( M2 ; M1 ) ...</k>  [:structural:]
rule <k> M1:#Magma includes ( M2:#Magma ) => subset( M2 ; M1 ) ...</k>  [:structural:]

rule <k> M1:#Magma excludes ( M2:#Magma ) => excludes( M1 ; M2 ) ...</k> [:structural:]
rule <k> M1:#Magma excludesAll ( M2:#Magma ) => excludes( M1 ; M2 ) ...</k> [:structural:]


/*@ 
 The evaluation of the \textsf{forAll} operator.\\
 The base case is trivial:
*/

rule <k> .Magma ->forAll(_| _) => true ...</k> [structural]

/*@ The  inductive step uses the substitution operator
  defined in the \textsf{SUBSTITUTION}. This requires the
 overloading the substitution operator to expressions:
*/

 syntax Exp ::=  Exp "[" #MagmaElement "/" #Id "]" [ditto]


rule <k>
       (S:#MagmaElement ;Magma Val:#Magma) ->forAll( Var:#Id | BEXP:Exp )
       => 
       if BEXP[S/Var] 
         then Val ->forAll( Var | BEXP)
         else false
       endif 
     ...</k> 
     [structural]

/*@ \paragraph{The \textsf{exists} operator.}
The base case:
*/

 rule  <k> .Magma ->exists(_| _) => false ...</k> [structural]

//@ The inductive step:

rule <k>
        (S ;Magma Val) ->exists( Var:#Id | BEXP:Exp )
        => 
       if BEXP[S/Var] 
         then true 
         else Val ->exists( Var | BEXP)
         endif 
     ...</k> 
     [structural]

/*@ \subsection{Semantics of String Expressions}
We have just one operator for now:
*/

 rule <k>  Str1:#String ++ Str2:#String => Str1 +String Str2 ...</k> [structural]

/*@ \subsection{Semantics of Collection Expressions}

Empty collection:
*/

rule <k> empty => .Magma ...</k> [structural]

/*@ \paragraph{The \textsf{allInstances(Class)} operator}
The evaluation of the operator uses the \K function
\textsf{children} from the \K definition of the metamodel
*/
 
rule <k> Cls:#Id .allInstances()
         =>
         collectAllInstanceNames((BagItem(Cls) children(Cls)), INST:Bag)
    ...</k>  
    <instances> INST </instances> [structural] 

/*@ \paragraph{Helper function \textsf{collectAllInstanceNames(Classes, INST)}}
Collects all the instances belonging to a class in \textsf{Classes} selected from
the bag of instances \textsf{INST}.
*/

// syntax #Magma ::= "collectAllInstanceNames" "(" Bag "," Bag ")" 

 declare collectAllInstanceNames : Bag Bag -> #Magma

//@ The base case:

 define collectAllInstanceNames(.Bag, _) => .Magma

//@ The inductive case:
 define collectAllInstanceNames(BagItem(Cls:#Id) Bg:Bag, INST)
      =>
      collectInstanceNames(Cls, INST) ;Magma collectAllInstanceNames(Bg, INST)

/*@ \paragraph{The \textsf{collectInstances} function}
Collects all the instances of a given class \textsf{Cls} from a bag \textsf{INST} 
of instances.
It uses the helper function defined above.
*/

 declare collectInstanceNames : #Id  Bag  -> #Magma

//@ The base case:

 define collectInstanceNames(Cls, .Bag) => .Magma

//@ The inductive case:

 define collectInstanceNames(Cls,
                           (<instance> 
                              <instName> INAME:#Id </instName> 
                              <ofClass> Cls </ofClass>
                             <attributes> _:Map </attributes>
                            </instance> 
                            REST:Bag ))
      => 
      ((INAME::Cls) ;Magma collectInstanceNames(Cls, REST))


 define collectInstanceNames(Cls, 
                           (<instance>... 
                              <ofClass> Cls':#Id </ofClass>
                            ...</instance> REST:Bag))
       =>
      collectInstanceNames(Cls, REST)  when notBool (Cls ==Bool Cls')
 


/*@ \paragraph{The  \textsf{CExp . Id} operator}
 We assume that each element in \textsf{CExp} has the attribute Id.
 \textcolor{red}{Should we report an error otherwise? If yes, then we should
 invent an exception mechanism. Alternatively, we
 may write a typechecker in the future to check that.}
*/
 


// The base case:
rule <k>  .Magma .AT:#Id  => .Magma ...</k> [:structural:]

// inductive step
rule <k> (((INAME::Cls) ;Magma Val) .AT) => Val':#Magma union ((Val) .AT) ...</k>
     <instance>
           <instName> INAME </instName>
           <ofClass> Cls </ofClass>
              //use its attribute values at AT
           <attributes>... AT |-> typedElt(Val', _) ...</attributes>
     </instance>  [structural]

//@ \paragraph{The \textsf{union} operator}

 rule <k> Val1:#Magma union Val2:#Magma   => union( Val1 ; Val2 ) ...</k> [structural]


/*@ \paragraph{The \textsf{collect} operator}
 Its semantics is similar to that of \textsf{forAll} and \textsf{exists}
*/

 rule <k> .Magma ->collect(_|_) => .Magma  ...</k> [structural]

rule <k>
       (S:#MagmaElement ;Magma Val) ->collect( Var:#Id | CEXP:Exp )
        =>
       Val ->collect( Var | CEXP)  union  CEXP[S/Var]
     ...</k>
     [structural]

/*@ \paragraph{The \textsf{select} operator}
 similar to collect
*/

rule <k>  .Magma ->select(_|_) =>  .Magma ...</k> [structural]

rule <k>  (S ;Magma Val)  ->select( Var | BEXP:Exp )
 => (if BEXP[S/Var] then S else .Magma endif) union (Val ->select(Var| BEXP:Exp ))  ...</k> [structural]

//@ \paragraph{The \textsf{let} operator} Its semantics is just a substitution.

rule <k> let  X:#Id =  CEXP1 in CEXP2  endlet => CEXP2[CEXP1/X] ...</k> [structural]

//@ \paragraph{The \textsf{if} operator}

rule <k> if true then CEXP1:Exp else CEXP2:Exp endif => CEXP1 ...</k> [structural]
rule <k> if false then CEXP1 else CEXP2 endif => CEXP2 ...</k> [structural]

end module

