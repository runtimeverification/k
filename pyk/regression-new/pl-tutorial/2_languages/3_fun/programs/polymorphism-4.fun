// testing polymorphism

let f = fun x -> let y = x in y
in (fun x -> f) 7

// identity
