// testing polymorphism and also the efficiency of the type inferencer

let f00 = fun x -> fun y -> x in
  let f01 = fun x -> f00 (f00 x) in
    let f02 = fun x -> f01 (f01 x) in
      let f03 = fun x -> f02 (f02 x) in
        let f04 = fun x -> f03 (f03 x) in
          f04
