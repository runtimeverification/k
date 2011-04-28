require  values

kmod META-MODEL is including K + PL-ID + VALUES

syntax K ::= Id

syntax Id ::= 
process
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

 syntax Bag ::= children ( Id )

rule children(process) => .Bag BagItem(activity) [structural]
rule children(activity) => .Bag  [structural]
rule children(workSequence) => .Bag  [structural]
rule children(resource) => .Bag  [structural]

 syntax Map ::= attributeDecl ( Id )

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


 syntax Bool ::= isEnum ( Id )

rule isEnum(activityState) => true [structural]
rule isEnum(timeState) => true [structural]
rule isEnum(Id:Id) => false if 
notBool(Id ==Bool timeState) andBool
notBool(Id ==Bool activityState) 
[structural]


 syntax Bag ::= values ( Id )

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


endkm
