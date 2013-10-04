// the program below justifies the restriction that reference
// types should not be polymorphic

// the following runs in our semantics, but it should not type
// (elements of different types are added in *r)!

let f = let r = ref []
        in (fun x -> r := cons x @r; x)
in if f true then f 3 else f 4
