 require ../../../k-prelude


/*
  The module OCL-SOLVER should include the syntax for OCL formulas and rules for evaluating them.
*/
kmod OCL-SOLVER is including K + PL-ID
  syntax Formula ::=  `True | `False | forAll ( OclVar : Id `| Bool )
  syntax OclVar ::= t`!
endkm

/*
  A meta-model consists of a configuration including 
     - the classes together with their relationships and
     - the OCL constraints, 
  and the set of rules describing the dynamic of the models.
  A model is represented by a cell including instances of the classes. For each instance, we have
  cells with the name of the instance, the name of the class owner, and the values of the attributes.
*/
kmod META-MODEL is including OCL-SOLVER

  syntax Id ::= object 

 
  syntax K ::= Id | undefined | Bool 

  syntax ListItem ::= Id : KLabel [prec 20] | Formula

  syntax Type ::= int | bool | string | Id

  syntax Bool ::= isScalar ( Type )

  rule isScalar(int) => true [structural]
  rule isScalar(bool) => true [structural]
  rule isScalar(string) => true [structural]
  rule isScalar(Id:Id) => false [structural]


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
                    <name> undefined </name> /*Vlad: added metamodel name*/
                    <classes>
                      <class*>
                         <className> undefined </className> /*Vlad: changed Id:Id to undefined because of errors in rule matching*/
                         <extends> undefined </extends> /*Vlad: changed Id:Id to undefined because of errors in rule matching*/
                         <declAttributes> .Map  </declAttributes>/*Vlad: I think we need a Map from attribute names to types here*/
                      </class*>
                    </classes>
                    <oclConstraints> .List </oclConstraints>
                  </metamodel*>
                 <models>
                   <model*> 
                      <modelName> undefined </modelName> /*Vlad: added model name*/
                      <instance*>
                         <instName> undefined </instName>
                         <ofClass> undefined </ofClass>
                         <attributes> .Map </attributes>
                      </instance*>
                   </model*>
                 </models>
                <k> .K </k> /*Vlad: added K cell for checking conformance */
                </T>

 
endkm







/* 
   A conformance checking traverses the model in parallel with the the configuration of the metamodel
   and checks if the instance is defined in accord with the definition of the class and whether the
   corresponding OCL constraints are satisfied.

  ... to be done ...
*/
