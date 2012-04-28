require /modules/unification


module UNIFICATION-TEST imports UNIFICATION
  syntax UnificationVar ::= "x1" | "x2" | "x3" | "x4"
  syntax Bag ::= "start" | "good"
  define start 
      => <k> applySubst(unify('h('g(x2),,'f(x1,,'h(x1),,x2)),'h(x1,,'f('g(x3),,x4,,x3))),x1) </k>
  define <k> 'g('x3(.List{K})) </k> => good
end module
