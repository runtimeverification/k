require values.maude
require meta-model-interface.k

module META-MODEL is
  including #MAGMA + META-MODEL-INTERFACE

syntax K ::= #Id

syntax #Id ::= process
| activity
| workSequence
| resource
| tS
| time
| time
| finishedToStart
| startedToStart
| startedToFinish
| activities
| activities
| available
| linkToPredecessor
| finishedToFinish
| resources
| aS
| tmax
| tmin
| activityState
| timeState
| finished
| undef
| tooLate
| notStarted
| inProgress
| ok
| tooEarly

// syntax Bag ::= children ( #Id )
// declare children : #Id -> Bag 
// all descendants of a class
rule children(process) => .Bag BagItem(activity) [structural]
rule [CHILDREN] : children(activity) => .Bag  [structural]
rule children(workSequence) => .Bag  [structural]
rule children(resource) => .Bag  [structural]
// define children(process) => BagItem(activity)
// define children(activity) => .Bag 
// define children(workSequence) => .Bag
// define children(resource) => .Bag 


// syntax Map ::= attributeDecl ( #Id )
// for each class, return a map (featureName |-> type)
rule attributeDecl(process) => .Map
(time |-> int)
(activities |-> activity)
[structural]

rule attributeDecl(activity) => .Map
(linkToPredecessor |-> workSequence)
(time |-> int)
(tmin |-> int)
(tmax |-> int)
(activities |-> activity)
(aS |-> activityState)
(tS |-> timeState)
(resources |-> resource)
[structural]

rule attributeDecl(workSequence) => .Map
(finishedToStart |-> activity)
(startedToStart |-> activity)
(finishedToFinish |-> activity)
(startedToFinish |-> activity)
[structural]

rule attributeDecl(resource) => .Map
(available |-> bool)
[structural]


// syntax #Bool ::= isEnum ( #Id )
// returns True iff Id is an enumeration name
rule isEnum(activityState) => true [structural]
rule isEnum(timeState) => true [structural]
rule isEnum(Id:#Id) => false when 
notBool(Id ==Bool timeState) andBool
notBool(Id ==Bool activityState) 
[structural]


// syntax Bag ::= values ( #Id )
//for each Id assumed to be an enumeration name, return its values
rule values(activityState) => .Bag
BagItem(notStarted)
BagItem(inProgress)
BagItem(finished)
[structural]

rule values(timeState) => .Bag
BagItem(tooEarly)
BagItem(ok)
BagItem(undef)
BagItem(tooLate)
[structural]


end module
