require ocl-semantics

kmod TEST is including OCL-SEMANTICS

syntax Id ::=  a | b | c |  modelM | attr1 | attr2 | attr3 | attr4  | attr5 |  classA | classB | classZ | x | y | z



syntax Bag ::= testConfig


macro testConfig = 
  <T>
    <metamodel>
      <name> undefined </name> 
      <classes>
        <class> 
          <className> classA </className> 
          <extends> object </extends>
          <declAttributes> attr1 |-> colInst attr3 |-> colInt </declAttributes>
        </class>
        <class>
          <className> classB </className> 
          <extends> object </extends>
          <declAttributes> attr2 |-> colInst attr4 |-> colString attr5 |-> colString  </declAttributes>
        </class>
      </classes>
      <oclConstraints> .List </oclConstraints> 
    </metamodel>
    <models>
      <model>
        <modelName> modelM </modelName>
          <instance>
            <instName>  a </instName>
            <ofClass>  classA </ofClass>
            <attributes>
               (attr1 |-> typedElt(val(BagItem(b : classB) BagItem(c : classB)), colInst))
               (attr3 |-> typedElt(val(BagItem(1)), colInt ))
            </attributes>
          </instance>
          <instance>
            <instName> b </instName>
            <ofClass> classB </ofClass>
            <attributes> 
             (attr2 |-> typedElt(val(BagItem(a : classA)), colInst))
             (attr4 |-> typedElt(val(BagItem("if")), colString))
             (attr5 |-> typedElt(val(BagItem(" and")), colString))
           </attributes>
          </instance>
        <instance>
            <instName> c </instName>
            <ofClass> classB </ofClass>
            <attributes> 
             (attr2 |-> typedElt(val(BagItem(a : classA)),  colInst))
             (attr4 |-> typedElt(val(BagItem("IF")), colString))
             (attr5 |-> typedElt(val(BagItem(" AND")), colString))
           </attributes>
          </instance>
       </model> 
     </models>
         <k> 
             (allInstances(classA)->forAll(x|(x#attr1)->forAll(y|(x in (y#attr2)))))
              and
             (allInstances(classB)->forAll(x|(x#attr2)->forAll(y|(x in (y#attr1)))))
              // these are incorrect versions of the "two unidirectional associations form a bidirectional one"
              // the correct version is
             //  (allInstances(classA)->forAll(x| (x#attr1)->forAll(y|((y isTypeOf classB) implies x in (y#attr2)))))
             //   and
              // (allInstances(classB)->forAll(x| (x#attr2)->forAll(y|((y isTypeOf classA) implies x in (y#attr1)))))
         </k>
         //<k>    (((allInstances(classB) ->collect(x | ( ((x # attr4) ++   (x # attr5)) ++ (" only" ++ " if")) ))
         //      ->collect(y | y ++ " or"))->select(z | true)) Including " else" </k>
        //<k>    allInstances(classB) ->collect(x | ( ((x # attr4) ++   (x # attr5)) ++ (" only" ++ " if"))) </k>
        //<k>    allInstances(classB) ->select(x | (a : classA) in (x # attr2)  ) </k>
        //<k>    allInstances(classB) ->exists(x | (a : classA) in (x # attr2)  ) </k>
       //<k>    allInstances(classB) ->collect(x | (x # attr2)) </k>
       //<k>    allInstances(classA) ->forAll(x | (x # attr3) = val(BagItem(a : classA))) </k>
       //  <k>     ((a : classA) # attr3) = val(BagItem(a : classA))  </k>
       // <k>      (a : classA) # attr3 = val(BagItem(a : classA)) </k> 
    // <k> let x =  val(BagItem(a : classA)) in (x # attr3) endlet  </k>
     <temp> .Bag </temp>
  </T>




endkm 