// This tail recursive program uses fixed memory, but can take a lot of
// computation/stack space if the semantics is not tail-recursive.
// Curiously, the tail recursion rule does not seem to be favoured by
// maude: (1) it is not applied, preferring to apply the normal
// environment-recovery rule; and (2) it slows down significantly
// this program (4-5 times!), because it makes maude's matcher slower.

datatype nothing = Nothing

let n = ref 1000
in letrec f Nothing = if @n>0 then n := @n - 1; f Nothing else 0
   in f Nothing
