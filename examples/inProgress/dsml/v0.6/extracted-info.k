// handwritten extracted info module for xSPEM
require ../../../../k-prelude

kmod EXTRACTED-INFO is including K + PL-ID + PL-INT + PL-STRING
// scalar values

syntax Bool ::= isScalar ( Val )
rule isScalar(I:Int) => true [structural]
rule isScalar(bbb:Bool) => true [structural]
rule isScalar(Str:String) => true [structural]
rule isScalar((obj:Id):(typ:Id))  => isEnumType(typ) [structural]

rule isScalar(val(C1)) => false [structural]


syntax Id ::= activityState | timeState 

// enumeration types
syntax Bool ::= isEnumType ( Id )
rule isEnumType(activityState) => true [structural]
rule isEnum(TypetimeState) => true [structural]

endkm