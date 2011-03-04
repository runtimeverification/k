require meta-model
require ocl-syntax
require values

kmod CONFORMANCE is including META-MODEL + OCL-SYNTAX + VALUES

// need to implement error reporting!!

kvar INSTANCES REST B RESTBAG RESTINSTANCES : Bag
kvar ATTRCLS ATTRINST Map Map' Map'' : Map 
kvar C T nm INSNAME attr : Id 
kvar OCL : List
kvar E : Exp
kvar v : Val

syntax K ::= checkConformance 


rule
<k> checkConformance => checkStructure(INSTANCES)~>checkOCL(OCL)<_/k> 
<metamodel_> <oclConstraints> OCL => . </oclConstraints> <_/metamodel>
<models> <model> <modelName> nm </modelName> INSTANCES </model> </models>


syntax K ::= checkStructure ( Bag )


rule <k> checkStructure(.Bag) => (.) <_/k> 



rule <k> checkStructure(
                    (<instance_> 
                      <attributes> ATTRINST </attributes>
                      <ofClass> C </ofClass> 
                    <_/instance>
                       ) REST)
         => 
         consistentAttributes(ATTRINST, ATTRCLS, INSTANCES)~>checkStructure(REST)
     <_/k>
 
 <metamodel_>
    <classes_>
     <class_>
       <className> C </className>
       <declAttributes> ATTRCLS </declAttributes>
     <_/class>
     <_/classes>
 <_/metamodel>
     <models> // one model only
      <model>
        <modelName> nm </modelName>
          INSTANCES
      </model>
     </models>
syntax K ::= consistentAttributes( Map , Map , Bag )

rule consistentAttributes( .Map, _, _ ) => . [structural]


// for scalar types : just check that the attribute is declared in metamodel
rule  consistentAttributes( (attr |->  typedElt(v,T)) Map',  
                            (attr |-> T ) Map'', B)
      =>
      consistentAttributes(Map',Map'',B)
      if notBool isClass(T)
      [structural]


//syntax K ::= toto

// for non-scalar types (classes or collections of classes) : check that instances are also 
// in the model and are of the correct (declared) type
rule  <k> consistentAttributes( (attr |->  typedElt(v,T)) Map',  
                            ((attr |-> T ) Map''), INSTANCES)
      => 
      allPresentAndWellTyped(v,T, INSTANCES)~>consistentAttributes(Map',Map'',INSTANCES)
      <_/k>
      if isClass(T)    
      [structural]


syntax Bool ::= isClass ( Id )
rule isClass(int) => false [structural]
rule isClass(bool) => false [structural]
rule isClass(string) => false [structural]
rule isClass(C) => true 
if (( C =/=Bool int) andBool (C =/=Bool bool) andBool  (C =/=Bool string)) [structural]


syntax K ::= allPresentAndWellTyped( Val , Id , Bag )

rule allPresentAndWellTyped(val(.Bag), _, _) => . [structural]
rule allPresentAndWellTyped(val(BagItem(INSNAME : T) RESTBAG), T, 
                (<instance>
                  <instName> INSNAME </instName>
                  <ofClass> T </ofClass>
                  <attributes> ATTRINST </attributes>
                 </instance> RESTINSTANCES )) 
     => 
       allPresentAndWellTyped(val(RESTBAG), T, 
                (<instance>
                  <instName> INSNAME </instName>
                  <ofClass> T </ofClass> 
                  <attributes> ATTRINST </attributes>
                 </instance> RESTINSTANCES )) 
    [structural]


syntax K ::= checkOCL ( List )

rule <k_> checkOCL(.) => . <_/k>   [structural]

syntax ListItem ::= `OCL ( Exp ) | result ( Val )

rule <k> checkOCL( OCL(E) L:List) => E~>checkOCL(L) <_/k>   [structural]

// when an expression finished evaluating, it is placed at the end of the ocl constraints list


//rule <k> v => .K <_/k>
//<metamodel_> <oclConstraints_> (.).List => result(v) </oclConstraints> <_/metamodel>  [structural]
endkm
