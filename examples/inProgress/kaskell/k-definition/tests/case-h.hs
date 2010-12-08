module CaseH where
  test1lhs = case "strlit" of { k -> e; _ -> e' }
  test1rhs = if (v==k) then e else e'

  test2lhs = case 24 of { k -> e; _ -> e' }
  test2rhs = if (v==k) then e else e'

  test3lhs = case 'x' of { k -> e; _ -> e' }
  test3rhs = if (v==k) then e else e'

{-
  Parses as:


-}
