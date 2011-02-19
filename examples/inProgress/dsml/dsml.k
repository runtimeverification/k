//require ../../../k-prelude
require ocl-syntax


/*
  A meta-model consists of a configuration including 
     - the classes together with their relationships and
     - the OCL constraints, 
  and the set of rules describing the dynamic of the models.
  A model is represented by a cell including instances of the classes. For each instance, we have
  cells with the name of the instance, the name of the class owner, and the values of the attributes.
*/
kmod META-MODEL is including OCL-SYNTAX

  syntax Id ::= object 

 
  syntax K ::= undefined  

  syntax ListItem ::= Id : KLabel [prec 20] 



  syntax Bool ::= isScalar ( Type )

  rule isScalar(int) => true [structural]
  rule isScalar(bool) => true [structural]
  rule isScalar(c:Class) => false [structural]
  rule isScalar(col(int)) => false [structural]
  rule isScalar(col(bool)) => false [structural]
  rule isScalar(col(Class)) => false [structural]


/*
  A configuration for a metamodel consists of two cells: one for classes and one for OCL constraints.
  The cell for classes is similar to that used in the definition of SKOOL and includes three cells: 
  name of the class, name of the immediate ancestor (=object if it is a base class), and a cell for
  the attribute declarations. The types of the attributes are specified as labels (meta-representation).
  The associations between classes are represented by attributes describing the roles, where the type
  of the attribute is chosen according to the multiplicity.
  The cell for OCL constraints includes a list of formulas.
*/

  configuration <T> 
                  <metamodel*>
                    <name> undefined </name> 
                    <classes>
                      <class*>
                         <className> undefined </className> 
                         <extends> undefined </extends>
                         <declAttributes> .Map  </declAttributes>
                      </class*>
                    </classes>
                    <oclConstraints> .K </oclConstraints>
                  </metamodel*>
                 <models>
                   <model*> 
                      <modelName> undefined </modelName>
                      <instance*>
                         <instName> undefined </instName>
                         <ofClass> undefined </ofClass>
                         <attributes> .Map </attributes>
                      </instance*>
                   </model*>
                 </models>
                <k> .K </k> 
                </T>

 
endkm







/* 
   A conformance checking traverses the model in parallel with the the configuration of the metamodel
   and checks if the instance is defined in accord with the definition of the class and whether the
   corresponding OCL constraints are satisfied.

  ... to be done ...
*/
