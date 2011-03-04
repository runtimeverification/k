require ../ocl-semantics
require ../conformance


kmod AUTOMATA is including OCL-SEMANTICS + CONFORMANCE


  

  syntax Id ::= initstate | state | automaton | transition
              | label | trace | dest | orig | in | out | name | active | automataMM

  
                 
/*
  rule [one-step-transition] :
       <instance_>
          <ofClass> automaton </ofClass>
          <attributes_>
            trace |-> (Tr:List{K} => Tr,, L:K)
            active |-> (X:K => Y:K)
          <_/attributes>
       <_/instance>
*/
/*
  the below info is redundant for transitions
  if we include description of the both states, then the loop transitions cannot hold
  because the current prototype does not faithfully implement KRAM (?)
       <instance>
          <name> X </name>
          <ofClass> state </ofClass>
          <attributes_>
            out |-> T:K
          <_/attributes>
       </instance> 

       <instance>
          <name> Y:K </name>
          <ofClass> state </ofClass>
          <attributes_>
            in |-> T:K
          <_/attributes>
       </instance> 
*/
/*
       <instance>
          <name> T:K </name>
          <ofClass> transition </ofClass>
          <attributes_>
            label |-> L
            orig |-> X
            dest |-> Y
          <_/attributes>
       </instance> 
*/

  syntax Id ::= a | b | s0 | s1 | t1 | t2 | t3 | simple


  
  syntax Bag ::= initConfig

  macro initConfig
        =
        <T>
           <metamodel>
                   <name> undefined </name> 
                   <classes>
                      <class>
                         <className> automaton </className>
                         <extends> object </extends>
                         <declAttributes> 
                             (trace |-> string)
                             (active |-> state)
                         </declAttributes>
                      </class>
                      <class>
                         <className> transition </className>
                         <extends> object </extends>
                         <declAttributes> 
                             (label |-> string) 
                             (orig  |-> state)
                             (dest  |-> state)
                         </declAttributes>
                      </class>
                      <class>
                         <className> state </className>
                         <extends> object </extends>
                         <declAttributes>  
                             (in  |-> transition)
                             (out |-> transition)
                         </declAttributes>
                      </class>
                   </classes>
                   <oclConstraints>  OCL(1)  </oclConstraints>
            </metamodel>
            <models>
               <model>
                <modelName> simple </modelName>
                   <instance> 
                      <instName> a </instName>
                      <ofClass> automaton </ofClass>
                      <attributes> 
                          (trace |-> typedElt(val(BagItem("")), string))
                          (active |->  typedElt(val(BagItem(s0:state)), state))
                      </attributes>
                  </instance>
                  <instance> 
                     <instName> s0 </instName>
                     <ofClass> state </ofClass>
                     <attributes> 
                         (in |-> typedElt(val(BagItem(t1:transition)), transition))
                         (out |-> typedElt(val(BagItem(t1:transition) BagItem(t2:transition)), transition))
                     </attributes>
                 </instance>
                 <instance> 
                     <instName> s1 </instName>
                     <ofClass> state </ofClass>
                     <attributes> 
                        (in |->  typedElt(val(BagItem(t2:transition) BagItem(t3:transition)), transition))
                        (out |->  typedElt(val(BagItem(t3:transition)), transition))
                     </attributes>
                 </instance> 
                 <instance> 
                     <instName> t1 </instName>
                     <ofClass> transition </ofClass>
                     <attributes> 
                        (label |->  typedElt(val(BagItem("a")), string))
                        (orig |-> typedElt(val(BagItem(s0:state)), state))
                        (dest |-> typedElt(val(BagItem(s0:state)), state))
                     </attributes>
                </instance>
                <instance> 
                    <instName> t2 </instName>
                    <ofClass> transition </ofClass>
                    <attributes> 
                        (label |-> typedElt(val(BagItem("")), string))
                        (orig |-> typedElt(val(BagItem(s0:state)), state))
                        (dest |-> typedElt(val(BagItem(s1:state)), state))
                   </attributes>
               </instance>
               <instance> 
                   <instName> t3 </instName>
                   <ofClass> transition </ofClass>
                   <attributes> 
                       (label |-> typedElt(val(BagItem("b")), string))
                       (orig |->  typedElt(val(BagItem(s1:state)), state))
                       (dest |->  typedElt(val(BagItem(s1:state)), state))
                  </attributes>
              </instance>
           </model>
        </models>
        <k> checkConformance </k>
        <mem> .Map </mem>
        <nextLoc> 0 </nextLoc>
        </T>

endkm


