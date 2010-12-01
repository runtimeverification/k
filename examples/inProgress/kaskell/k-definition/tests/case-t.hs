module CaseT where
  test1lhs = case () of { () | p <- e0 -> e; _ -> e' }
  test1rhs = case e0 of { p -> e; _ -> e' }


{-
  Parse as



  After transformation

-}