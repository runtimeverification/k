require  values

kmod META-MODEL is including K + PL-ID + VALUES

syntax K ::= Id

syntax Id ::= 
automaton
| transition
| state
| initialState
| out
| trace
| in
| dest
| label
| active
| orig
| in
| out

 syntax Bag ::= children ( Id )

rule children(automaton) => .Bag  [structural]
rule children(transition) => .Bag  [structural]
rule children(state) => .Bag BagItem(initialState) [structural]
rule children(initialState) => .Bag  [structural]

 syntax Map ::= attributeDecl ( Id )

rule attributeDecl(automaton) => .Map
(active |-> state)
(trace |-> string)
[structural]

rule attributeDecl(transition) => .Map
(dest |-> state)
(orig |-> state)
(label |-> string)
[structural]

rule attributeDecl(state) => .Map
(out |-> transition)
(in |-> transition)
[structural]

rule attributeDecl(initialState) => .Map
(out |-> transition)
(in |-> transition)
[structural]


 syntax Bool ::= isEnum ( Id )

rule isEnum(Id:Id) => false [structural]

 syntax Bag ::= values ( Id )

rule values(Id) => .Bag [structural]

endkm
