callcc (fun $k -> (fun throw ->
  callcc (fun $k -> (fun throw -> 10)
                    (fun x -> $k (throw 20))
         )
                  )
                  (fun y -> $k 30)
       )

//try (
//  try (
//    10
//  ) catch(x) (
//    throw 20
//  )
//) catch(y) ( 30 )
