require ../conformance

kmod  XSPEM  is including CONFORMANCE

syntax Id ::= x | y 

syntax Id ::= onexSPEM
 | p
 | a
 | b
 | r
 | w1
 | w2


syntax Bag ::= initConfig

 macro initConfig = 
<T>
	<oclConstraints>
		OCL(((allInstances(process).size()) = 1))

		OCL(allInstances(activity)->forAll(x |(x#linkToPredecessor).size() >= 1))
		OCL(allInstances(activity)->forAll(x |(x#linkToPredecessor).size() <= 1))
		.List
	</oclConstraints>
<models>
	<model>
	<modelName> onexSPEM </modelName> 
		<instance>
			<instName> p </instName>
			<ofClass> process </ofClass>
			<attributes>
				(time |-> typedElt(val(BagItem(0)),int))
				(activities |-> typedElt(val(.Bag  BagItem(a:activity) BagItem(b:activity)),activity))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> a </instName>
			<ofClass> activity </ofClass>
			<attributes>
				(tmin |-> typedElt(val(BagItem(5)),int))
				(tmax |-> typedElt(val(BagItem(8)),int))
				(aS |-> typedElt(val(BagItem(notStarted)),activityState))
				(tS |-> typedElt(val(BagItem(undef)),timeState))
				(resources |-> typedElt(val(.Bag  BagItem(r:resource)),resource))
				(time |-> typedElt(val(BagItem(0)),int))
				(linkToPredecessor |-> typedElt(val(.Bag  BagItem(w2:workSequence)),workSequence))
				(activities |-> typedElt(val(.Bag ),activity))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> b </instName>
			<ofClass> activity </ofClass>
			<attributes>
				(tmin |-> typedElt(val(BagItem(5)),int))
				(tmax |-> typedElt(val(BagItem(8)),int))
				(aS |-> typedElt(val(BagItem(notStarted)),activityState))
				(tS |-> typedElt(val(BagItem(undef)),timeState))
				(resources |-> typedElt(val(.Bag  BagItem(r:resource)),resource))
				(time |-> typedElt(val(BagItem(0)),int))
				(linkToPredecessor |-> typedElt(val(.Bag  BagItem(w1:workSequence)),workSequence))
				(activities |-> typedElt(val(.Bag ),activity))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> r </instName>
			<ofClass> resource </ofClass>
			<attributes>
				(available |-> typedElt(val(BagItem(true)),bool))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> w1 </instName>
			<ofClass> workSequence </ofClass>
			<attributes>
				(startedToStart |-> typedElt(val(.Bag ),activity))
				(startedToFinish |-> typedElt(val(.Bag ),activity))
				(finishedToStart |-> typedElt(val(.Bag ),activity))
				(finishedToFinish |-> typedElt(val(.Bag  BagItem(a:activity)),activity))
				.Map
			</attributes>
		</instance>
		<instance>
			<instName> w2 </instName>
			<ofClass> workSequence </ofClass>
			<attributes>
				(startedToStart |-> typedElt(val(.Bag ),activity))
				(startedToFinish |-> typedElt(val(.Bag ),activity))
				(finishedToStart |-> typedElt(val(.Bag ),activity))
				(finishedToFinish |-> typedElt(val(.Bag ),activity))
				.Map
			</attributes>
		</instance>
	</model>
</models>
<k>  checkConformance </k>
<output>  .List </output>
<mem>  .Map </mem>
<nextLoc>  0 </nextLoc>
</T>
endkm
