require meta-model
require ocl-syntax
require values

kmod CONFORMANCE is including META-MODEL + OCL-SYNTAX + VALUES

// need to implement error reporting!!

kvar INSTANCES REST B RESTBAG RESTINSTANCES : Bag
kvar ATTRCLS ATTRINST Map Map' Map'' : Map 
kvar C T nm INSNAME attr x : Id 
kvar OCL : List
kvar LL : List{Id}
kvar E : Exp
kvar v : Val

syntax K ::= checkConformance 


rule

<k> checkConformance => checkStructure(INSTANCES)~>checkOCL(OCL)<_/k> 
<metamodel_> <oclConstraints> OCL => . </oclConstraints> <_/metamodel>
<models> <model> <modelName> nm </modelName> INSTANCES </model> </models>


//<k> checkConformance => checkOCL(OCL)<_/k> 
//<metamodel_> <oclConstraints> OCL </oclConstraints> <_/metamodel>



syntax K ::= checkStructure ( Bag )


rule <k> checkStructure(.Bag) => (.) <_/k> 



rule <k> checkStructure(
                    (<instance_>            
                      <attributes> ATTRINST </attributes>
                      <ofClass> C </ofClass> 
                    <_/instance>
                       ) REST)
         => 
         consistentAttributes(ATTRINST, ATTRCLS)~>checkStructure(REST)
     <_/k>
 <metamodel_>
    <classes_>
     <class_>
       <className> C </className>
       <declAttributes> ATTRCLS </declAttributes>
     <_/class>
     <_/classes>
 <_/metamodel>


syntax K ::= consistentAttributes( Map , Map )

rule <k> consistentAttributes( .Map, _ ) => . <_/k> 


// for basic types : just check that the attribute is declared in metamodel
rule  <k> consistentAttributes( (attr |->  typedElt(v,T)) Map',  
                            (attr |-> T ) Map'')
      =>
      consistentAttributes(Map',Map'') <_/k>
      if isBasic(T)


//for enumerations : check that the attribute is declared with same enum type; check value
//assumption (made in metamodels) : no class and enum have same name
rule  <k> consistentAttributes( (attr |->  typedElt(val(BagItem(x)),T)) Map',  
                            (attr |-> T ) Map'')
      =>
      consistentAttributes(Map',Map'') <_/k>
<metamodel_>
    <classes_>
     <enumeration_>
       <enumName> T </enumName>
        BagItem(x)
     <_/enumeration>
     <_/classes>
 <_/metamodel>
      if notBool isBasic(T)


// for classes or collections : check that instances are also 
// in the model and are of the correct (declared) type
rule  <k> consistentAttributes( (attr |->  typedElt(v,T)) Map',  //T here may be a subtype of
                            (attr |-> T ) Map'')   // T here
      => 
      allPresentAndWellTyped(v)~>consistentAttributes(Map',Map'')
      <_/k>
<metamodel_>
    <classes_>
     <class_>
       <className> T </className>
     <_/class>
     <_/classes>
 <_/metamodel>
      if notBool isBasic (T)    
      [structural]

//or of a supertype
rule  <k> consistentAttributes( (attr |->  typedElt(v,T)) Map',  
                            ((attr |-> T':Id ) Map''))
      => 
       allPresentAndWellTyped(v)~>consistentAttributes(Map',Map'')
      <_/k>
<metamodel_>
    <classes_>
     <class_>
       <className> T </className>
         <extends> BagItem(T') _ </extends>
     <_/class>
     <_/classes>
 <_/metamodel>
      if notBool(isBasic(T)) andBool notBool (T ==Bool T')
      [structural]


syntax Bool ::= isBasic ( Id )
rule isBasic(int) => true [structural]
rule isBasic(bool) => true [structural]
rule isBasic(string) => true [structural]
rule isBasic(C) => false
if (( C =/=Bool int) andBool (C =/=Bool bool) andBool  (C =/=Bool string)) [structural]




syntax K ::= allPresentAndWellTyped( Val )
// all elements in a collection must exist as such among instances (including classes)
rule <k> allPresentAndWellTyped(val(.Bag)) => . <_/k> 

rule <k> allPresentAndWellTyped(val(BagItem(INSNAME : T) RESTBAG)) =>  
         allPresentAndWellTyped(val(RESTBAG))
     <_/k>
<models> 
  <model_> 
       <instance_>
       <instName> INSNAME </instName>
        <ofClass> T </ofClass>
      <_/instance>
  <_/model> 
</models> 



syntax K ::= checkOCL ( List )

rule <k> checkOCL(.) => . <_/k>   [structural]

syntax ListItem ::= `OCL ( Exp ) | result ( Val )

rule <k> checkOCL( OCL(E) L:List) => E~>checkOCL(L) <_/k>   [structural]
// when an expression finished evaluating, it is placed at the end of the ocl constraints list

// comment  when "executing" a model
rule <k> v => .K <_/k>
//<metamodel_> <oclConstraints_> (.).List => result(v) </oclConstraints> <_/metamodel>  [structural]

<output_> (.).List => result(v) </output>   [structural]
endkm
