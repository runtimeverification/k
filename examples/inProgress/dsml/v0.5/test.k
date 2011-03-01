require ocl-semantics

kmod TEST is including OCL-SEMANTICS

syntax Id ::=  a | b | c | d |  modelM | attr1 | attr2 | attr3 | attr4  | attr5 |  classA | classB | classZ 
| x | y | z | int | bool | string 



syntax Bag ::= testConfig


macro testConfig = 
  <T>
    <metamodel>
      <name> undefined </name> 
      <classes>
        <class> 
          <className> classA </className> 
          <extends> object </extends>
          <declAttributes> attr1 |-> classB attr3 |-> int </declAttributes>
        </class>
        <class>
          <className> classB </className> 
          <extends> object </extends>
          <declAttributes> attr2 |-> classA attr4 |-> string attr5 |-> string  </declAttributes>
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
               (attr1 |-> typedElt(val(BagItem(c : classB) BagItem(d : classB)), classB))
               (attr3 |-> typedElt(val(BagItem(1)), int ))
            </attributes>
          </instance>
           <instance>
            <instName>  b </instName>
            <ofClass>  classA </ofClass>
            <attributes>
               (attr1 |-> typedElt(val(BagItem(c : classB)), classB))
               (attr3 |-> typedElt(val(BagItem(2)), int ))
            </attributes>
          </instance>
          <instance>
            <instName> c </instName>
            <ofClass> classB </ofClass>
            <attributes> 
             (attr2 |-> typedElt(val(BagItem(c : classB)), classB))
             (attr4 |-> typedElt(val(BagItem("if")), string))
             (attr5 |-> typedElt(val(BagItem(" and")), string))
           </attributes>
          </instance>
        <instance>
            <instName> d </instName>
            <ofClass> classB </ofClass>
            <attributes> 
             (attr2 |-> typedElt(val(BagItem(b : classA)),  classA))
             (attr4 |-> typedElt(val(BagItem("if")), string))
             (attr5 |-> typedElt(val(BagItem(" AND")), string))
           </attributes>
          </instance>
       </model> 
     </models>


<k> allInstances(classB)->forAll(x| (x#attr2)->forAll(y|((oclType(y) =  classA) implies ((y#attr1) includes x))))</k>
//
// this one fails: see correct version above 
//<k>  allInstances(classB) ->forAll(x|(x#attr2)  ->forAll(z|   ((z # attr1)  includes x )))   </k>
   /*     
         <k>   
              ((allInstances(classB) ->collect(x | ( ((x # attr4)  ++   (x # attr5)) ++ (" only" ++ " if")) ))
                ->collect(y | y ++ " or"))->select(z | z.size()  = 1)
         </k>
   */      
       // <k>    empty union ((allInstances(classB) ->collect(x | ( ((x # attr4) ++   (x # attr5)) ++ (" only" ++ " if")))).size()) </k>
        // <k>    allInstances(classB) ->select(x |  (x # attr2) includes  (a : classA) ) </k>
      //<k>    allInstances(classB)->collect(x | (x # attr2)) </k>
       // <k>    allInstances(classA) ->forAll(x | (x # attr3) <= 2) </k>
       //<k>    allInstances(classB) ->exists(x | (x # attr2) = (a : classA)) </k>
       //<k> allInstances(classA)->select(x | ((x#attr3) >= 2)) </k>
     // <k> let x =  (a : classA) in (x#attr3) = 1  endlet  </k>
     <temp> .Bag </temp>
     <comp> .Bag </comp>
  </T>




endkm 