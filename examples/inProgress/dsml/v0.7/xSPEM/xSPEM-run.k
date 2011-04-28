require xSPEM

kmod XSPEM-RUN is including XSPEM +  K-CONDITION-SEARCH


rule
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
<modelName> nM:Id </modelName>
<instance>
	<instName> X:Id </instName>
	<ofClass> process </ofClass>
	<attributes>
		(time |-> (typedElt(val(BagItem(TT:Int)),int)))
		MM1:Map
	</attributes>
</instance>
B:Bag
</model>
</models>
<k> run </k>
<output> .List </output> 
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>
=>
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
<modelName> nM:Id </modelName>
<instance>
	<instName> X:Id </instName>
	<ofClass> process </ofClass>
	<attributes>
		(time |-> (typedElt(val(BagItem(res:Int)),int)))
		MM1:Map
	</attributes>
</instance>
B:Bag
</model>
</models>
<k> run </k>
<output> .List </output> 
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>
if
search
(
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
<modelName> nM:Id </modelName>
<instance>
	<instName> X:Id </instName>
	<ofClass> process </ofClass>
	<attributes>
		(time |-> (typedElt(val(BagItem(TT:Int)),int)))
		MM1:Map
	</attributes>
</instance>
B:Bag
</model>
</models>
<k> checkOCL(OCL(TT:Int + 1)) </k>
<output> .List </output> 
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>
=>
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
<modelName> nM:Id </modelName>
<instance>
	<instName> X:Id </instName>
	<ofClass> process </ofClass>
	<attributes>
		(time |-> (typedElt(val(BagItem(TT:Int)),int)))
		MM1:Map
	</attributes>
</instance>
B:Bag
</model>
</models>
<k> .K </k>
<output> result(res:Int) </output> 
<nextLoc> III:Int </nextLoc>
<mem> .Map</mem>
</T>
)


// start rule
rule 
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
  	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(time |-> typedElt(val(BagItem(TT:Int)),int))
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
	</instance>
	<instance>
		<instName> Y:Id </instName>
		<ofClass> activity </ofClass>
		<attributes>
			(time |-> typedElt(val(BagItem(0)),int))
			(aS |-> typedElt(val(BagItem(notStarted:activityState)),activityState))
			(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
			MM2:Map
		</attributes>
	</instance>
	B:Bag
</model>
</models>
<k> run </k>
<output> .List </output> 
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>
=>
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(time |-> typedElt(val(BagItem(TT:Int)),int))
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
	</instance>
	<instance>
		<instName> Y:Id </instName>
		<ofClass> activity </ofClass>
		<attributes>
			(time |-> typedElt(val(BagItem(TT:Int)),int))
			(aS |-> typedElt(val(BagItem(inProgress:activityState)),activityState))
			(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
			MM2:Map
		</attributes>
	</instance>
	B:Bag
</model>
</models>
<k> run </k>
<output> .List </output> 
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>
if 
search((
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(time |-> typedElt(val(BagItem(TT:Int)),int))
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
	</instance>
	<instance>
		<instName> Y:Id </instName>
		<ofClass> activity </ofClass>
		<attributes>
			(time |-> typedElt(val(BagItem(0)),int))
			(aS |-> typedElt(val(BagItem(notStarted:activityState)),activityState))
			(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
			MM2:Map
		</attributes>
	</instance>
	B:Bag
</model>
</models> 
<k> 
 checkOCL
(
    OCL(
         (((((Z:Id):workSequence)#finishedToStart)->forAll(x| ((x#aS) = (finished:activityState))))
         and
          ((((Z:Id):workSequence)#startedToStart)->forAll(x| ((x#aS) = (inProgress:activityState)))))
         and 
          ((((Y:Id):activity)#resources)->forAll(x| (x#available) = true))
       )
)
</k>
<output> .List </output>
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>)
=>
(
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(time |-> typedElt(val(BagItem(TT:Int)),int))
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
		</instance>
		<instance>
			<instName> Y:Id </instName>
			<ofClass> activity </ofClass>
			<attributes>
				(time |-> typedElt(val(BagItem(0)),int))
				(aS |-> typedElt(val(BagItem(notStarted:activityState)),activityState))
				(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
				MM2:Map
			</attributes>
		</instance>
		B:Bag
</model>
</models> 
<k> .K </k>
<output> result(true) </output>
<nextLoc> N:Nat </nextLoc>
<mem> .Map</mem>
</T>))


//finishing an activity: too early
rule 
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
  	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
	</instance>
	<instance>
		<instName> Y:Id </instName>
		<ofClass> activity </ofClass>
		<attributes>
			(aS |-> typedElt(val(BagItem(inProgress:activityState)),activityState))
                        (tS |-> typedElt(val(BagItem(undef:timeState)),timeState))
			(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
			MM2:Map
		</attributes>
	</instance>
	B:Bag
</model>
</models>
<k> run </k>
<output> .List </output> 
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>
=>
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
	</instance>
	<instance>
		<instName> Y:Id </instName>
		<ofClass> activity </ofClass>
		<attributes>
			(aS |-> typedElt(val(BagItem(finished:activityState)),activityState))
                        (tS |-> typedElt(val(BagItem(tooEarly:timeState)),timeState))
			(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
			MM2:Map
		</attributes>
	</instance>
	B:Bag
</model>
</models>
<k> run </k>
<output> .List </output> 
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>
if 
search((
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
	</instance>
	<instance>
		<instName> Y:Id </instName>
		<ofClass> activity </ofClass>
		<attributes>
			(aS |-> typedElt(val(BagItem(inProgress:activityState)),activityState))
                        (tS |-> typedElt(val(BagItem(undef:timeState)),timeState))
			(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
			MM2:Map
		</attributes>
	</instance>
	B:Bag
</model>
</models> 
<k> 

 checkOCL
(
    OCL(
         (((((Z:Id):workSequence)#startedToFinish)->forAll(x| ((x#aS) = (inProgress:activityState))))
         and
          ((((Z:Id):workSequence)#finishedToFinish)->forAll(x| ((x#aS) = (finished:activityState)))))
         and
         ((((X:Id):process)#time) < ((((Y:Id):activity)#time) + (((Y:Id):activity)#tmin)))
       )
)
</k>
<output> .List </output>
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>)
=>
(
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
		</instance>
		<instance>
			<instName> Y:Id </instName>
			<ofClass> activity </ofClass>
			<attributes>
				(aS |-> typedElt(val(BagItem(inProgress:activityState)),activityState))
                   		(tS |-> typedElt(val(BagItem(undef:timeState)),timeState))
				(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
				MM2:Map
			</attributes>
		</instance>
		B:Bag
</model>
</models> 
<k> .K </k>
<output> result(true) </output>
<nextLoc> N:Nat </nextLoc>
<mem> .Map</mem>
</T>))


//finishing an activity: ok
rule 
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
  	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
	</instance>
	<instance>
		<instName> Y:Id </instName>
		<ofClass> activity </ofClass>
		<attributes>
			(aS |-> typedElt(val(BagItem(inProgress:activityState)),activityState))
                        (tS |-> typedElt(val(BagItem(undef:timeState)),timeState))
			(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
			MM2:Map
		</attributes>
	</instance>
	B:Bag
</model>
</models>
<k> run </k>
<output> .List </output> 
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>
=>
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
	</instance>
	<instance>
		<instName> Y:Id </instName>
		<ofClass> activity </ofClass>
		<attributes>
			(aS |-> typedElt(val(BagItem(finished:activityState)),activityState))
                        (tS |-> typedElt(val(BagItem(ok:timeState)),timeState))
			(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
			MM2:Map
		</attributes>
	</instance>
	B:Bag
</model>
</models>
<k> run </k>
<output> .List </output> 
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>
if 
search((
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
	</instance>
	<instance>
		<instName> Y:Id </instName>
		<ofClass> activity </ofClass>
		<attributes>
			(aS |-> typedElt(val(BagItem(inProgress:activityState)),activityState))
                        (tS |-> typedElt(val(BagItem(undef:timeState)),timeState))
			(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
			MM2:Map
		</attributes>
	</instance>
	B:Bag
</model>
</models> 
<k> 

 checkOCL
(
    OCL(
         ((((((Z:Id):workSequence)#startedToFinish)->forAll(x| ((x#aS) = (inProgress:activityState))))
         and
          ((((Z:Id):workSequence)#finishedToFinish)->forAll(x| ((x#aS) = (finished:activityState)))))
         and
         ((((X:Id):process)#time) >= ((((Y:Id):activity)#time) + (((Y:Id):activity)#tmin))))
         and 
         ((((X:Id):process)#time) < ((((Y:Id):activity)#time) + (((Y:Id):activity)#tmax)))
       )
)
</k>
<output> .List </output>
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>)
=>
(
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
		</instance>
		<instance>
			<instName> Y:Id </instName>
			<ofClass> activity </ofClass>
			<attributes>
				(aS |-> typedElt(val(BagItem(inProgress:activityState)),activityState))
                   		(tS |-> typedElt(val(BagItem(undef:timeState)),timeState))
				(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
				MM2:Map
			</attributes>
		</instance>
		B:Bag
</model>
</models> 
<k> .K </k>
<output> result(true) </output>
<nextLoc> N:Nat </nextLoc>
<mem> .Map</mem>
</T>))


//finishing an activity: too late
rule 
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
  	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
	</instance>
	<instance>
		<instName> Y:Id </instName>
		<ofClass> activity </ofClass>
		<attributes>
			(aS |-> typedElt(val(BagItem(inProgress:activityState)),activityState))
                        (tS |-> typedElt(val(BagItem(undef:timeState)),timeState))
			(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
			MM2:Map
		</attributes>
	</instance>
	B:Bag
</model>
</models>
<k> run </k>
<output> .List </output> 
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>
=>
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
	</instance>
	<instance>
		<instName> Y:Id </instName>
		<ofClass> activity </ofClass>
		<attributes>
			(aS |-> typedElt(val(BagItem(finished:activityState)),activityState))
                        (tS |-> typedElt(val(BagItem(tooLate:timeState)),timeState))
			(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
			MM2:Map
		</attributes>
	</instance>
	B:Bag
</model>
</models>
<k> run </k>
<output> .List </output> 
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>
if 
search((
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
	</instance>
	<instance>
		<instName> Y:Id </instName>
		<ofClass> activity </ofClass>
		<attributes>
			(aS |-> typedElt(val(BagItem(inProgress:activityState)),activityState))
                        (tS |-> typedElt(val(BagItem(undef:timeState)),timeState))
			(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
			MM2:Map
		</attributes>
	</instance>
	B:Bag
</model>
</models> 
<k> 

 checkOCL
(
    OCL(
         (((((Z:Id):workSequence)#startedToFinish)->forAll(x| ((x#aS) = (inProgress:activityState))))
         and
          ((((Z:Id):workSequence)#finishedToFinish)->forAll(x| ((x#aS) = (finished:activityState)))))
         and
         ((((X:Id):process)#time) > ((((Y:Id):activity)#time) + (((Y:Id):activity)#tmax)))
       )
)
</k>
<output> .List </output>
<nextLoc> 0 </nextLoc>
<mem> .Map</mem>
</T>)
=>
(
<T>
<oclConstraints> .List </oclConstraints>
<models>
<model>
	<modelName> mNam:Id </modelName>
	<instance>
		<instName> X:Id </instName>
		<ofClass> process </ofClass>
		<attributes>
			(activities |-> typedElt(val(BagItem((Y:Id):activity) BB:Bag),activity))
			MM1:Map
		</attributes>
		</instance>
		<instance>
			<instName> Y:Id </instName>
			<ofClass> activity </ofClass>
			<attributes>
				(aS |-> typedElt(val(BagItem(inProgress:activityState)),activityState))
                   		(tS |-> typedElt(val(BagItem(undef:timeState)),timeState))
				(linkToPredecessor |-> typedElt(val(BagItem((Z:Id):workSequence)),workSequence))
				MM2:Map
			</attributes>
		</instance>
		B:Bag
</model>
</models> 
<k> .K </k>
<output> result(true) </output>
<nextLoc> N:Nat </nextLoc>
<mem> .Map</mem>
</T>))


// ad-hoc predicates for search

syntax Bool ::= allFinishedAndOk( Bag )

rule allFinishedAndOk
(<T_>
 <models> <model> <modelName> _:Id </modelName> .Bag </model> </models> 
<_/T>) => true [structural]

rule allFinishedAndOk(
<T>
<oclConstraints> LL1:List </oclConstraints>
<models> 
<model>
<modelName> nM:Id </modelName>
<instance>
  <ofClass> activity </ofClass>
  <attributes_>
      (aS|->(typedElt(val(BagItem((finished:activityState))),activityState)))
      (tS|->(typedElt(val(BagItem((ok:timeState))),timeState)))
  <_/attributes>
<_/instance>
B:Bag 
</model>
</models>
<k> kk:K </k>
<mem> MM:Map </mem>
<output> LL:List </output>
<nextLoc> NNN:Int </nextLoc>
</T> ) => 
allFinishedAndOk(
<T>
<oclConstraints> LL1:List </oclConstraints>
<models> 
<model>
<modelName> nM:Id </modelName>
B:Bag 
</model>
</models>
<k> kk:K </k>
<mem> MM:Map </mem>
<output> LL:List </output>
<nextLoc> NNN:Int </nextLoc>
</T>
) [structural]

rule allFinishedAndOk(
<T>
<oclConstraints> LL1:List </oclConstraints>
<models> 
<model>
<modelName> nM:Id </modelName>
<instance_>
  <ofClass> X:Id </ofClass>
<_/instance>
B:Bag 
</model>
</models>
<k> kk:K </k>
<mem> MM:Map </mem>
<output> LL:List </output>
<nextLoc> NNN:Int </nextLoc>
</T> ) => 
allFinishedAndOk(
<T>
<oclConstraints> LL1:List </oclConstraints>
<models> 
<model>
<modelName> nM:Id </modelName>
B:Bag 
</model>
</models>
<k> kk:K </k>
<mem> MM:Map </mem>
<output> LL:List </output>
<nextLoc> NNN:Int </nextLoc>
</T>
) 
if notBool (X:Id ==Bool activity)
[structural]


rule allFinishedAndOk(
<T_>
 <models> <model_>
<instance_>
  <attributes_>
      (aS|->(typedElt(val(BagItem(((X:Id):activityState))),activityState)))
  <_/attributes>
<_/instance>
<_/model>
</models>
<_/T> ) => false 
if notBool (X:Id ==Bool finished)
[structural]


rule allFinishedAndOk(
<T_>
 <models> <model_>
<instance_>
  <attributes_>
      (tS|->(typedElt(val(BagItem(((X:Id):timeState))),timeState)))
  <_/attributes>
<_/instance>
<_/model>
</models>
BB:Bag 
<_/T> ) => false 
if notBool (X:Id ==Bool ok)
[structural]

endkm