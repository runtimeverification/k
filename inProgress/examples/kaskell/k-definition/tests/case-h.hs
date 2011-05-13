module CaseH where
  test1lhs = case v of { "strlit" -> e; _ -> e' }
  test1rhs = if (v=="strlit") then e else e'

  -- test2lhs = case v of { 'x' -> e; _ -> e' }
  -- test2rhs = if (v=='x') then e else e'

  -- test3lhs = case v of { 22 -> e; _ -> e' }
  -- test3rhs = if (v==22) then e else e'

{-
  Parses as:

  Test1:
 (Module (SrcLoc "tests/case-h.hs" 1 1) (ModuleName "CaseH") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-h.hs" 2 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-h.hs" 2 26) (PLit (String "strlit")) (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-h.hs" 2 41) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-h.hs" 3 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (If (Paren (InfixApp (Var (UnQual (Ident "v"))) (QVarOp (UnQual (Symbol "=="))) (Lit (String "strlit")))) (Var (UnQual (Ident "e"))) (Var (UnQual (Ident "e'"))))) (BDecls ([]))) ([]))))


  Test2:

  Test3:

  After transformation:

  Test1:
 (Module (SrcLoc "tests/case-h.hs" 1 1) (ModuleName "CaseH") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-h.hs" 2 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (If (Paren (InfixApp (Var (UnQual (Ident "v"))) (QVarOp (UnQual (Symbol "=="))) (Lit (String "strlit")))) (Var (UnQual (Ident "e"))) (Var (UnQual (Ident "e'"))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-h.hs" 3 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (If (Paren (InfixApp (Var (UnQual (Ident "v"))) (QVarOp (UnQual (Symbol "=="))) (Lit (String "strlit")))) (Var (UnQual (Ident "e"))) (Var (UnQual (Ident "e'"))))) (BDecls ([]))) ([]))))

  Test2:

  Test3:


-}
