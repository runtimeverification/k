module Test(test) where

test = let f00 = \x -> \y -> x in
  let f01 = \x -> f00 (f00 x) in
    let f02 = \x -> f01 (f01 x) in
      let f03 = \x -> f02 (f02 x) in
        let f04 = \x -> f03 (f03 x) in
          let f05 = \x -> f04 (f04 x) in
            let f06 = \x -> f05 (f05 x) in
              let f07 = \x -> f06 (f06 x) in
                let f08 = \x -> f07 (f07 x) in
                  let f09 = \x -> f08 (f08 x) in
                    let f10 = \x -> f09 (f09 x) in
                      let f11 = \x -> f10 (f10 x) in
                        let f12 = \x -> f11 (f11 x) in
                          let f13 = \x -> f12 (f12 x) in
                            let f14 = \x -> f13 (f13 x) in
                              let f15 = \x -> f14 (f14 x) in
                                f15

