callcc (fun k -> (fun throw ->

//try (
  try (
    10
  ) catch(x) (
    throw 20
  )
//) catch(y) ( 30 )

) (fun y -> $k 30))
