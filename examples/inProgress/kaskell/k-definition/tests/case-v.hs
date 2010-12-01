module CaseV where
  test1rhs = case () of { () | e0 -> e ; _ -> e' }
  test2rhs = if e0 then e else e'

{-
  Parses as:
 (Module (SrcLoc "tests/case-v.hs" 1 1) (ModuleName "CaseV") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-v.hs" 2 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Case (Con (Special UnitCon)) ((:)(Alt (SrcLoc "tests/case-v.hs" 2 27) (PApp (Special UnitCon) ([])) (GuardedAlts ((:)(GuardedAlt (SrcLoc "tests/case-v.hs" 2 30) ((:)(Qualifier (Var (UnQual (Ident "e0")))) ([])) (Var (UnQual (Ident "e")))) ([]))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-v.hs" 2 42) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-v.hs" 3 3) (PVar (Ident "test2rhs")) Nothing (UnGuardedRhs (If (Var (UnQual (Ident "e0"))) (Var (UnQual (Ident "e"))) (Var (UnQual (Ident "e'"))))) (BDecls ([]))) ([]))))


  After transformation:
 (Module (SrcLoc "tests/case-v.hs" 1 1) (ModuleName "CaseV") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-v.hs" 2 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (If (Var (UnQual (Ident "e0"))) (Var (UnQual (Ident "e"))) (Var (UnQual (Ident "e'"))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-v.hs" 3 3) (PVar (Ident "test2rhs")) Nothing (UnGuardedRhs (If (Var (UnQual (Ident "e0"))) (Var (UnQual (Ident "e"))) (Var (UnQual (Ident "e'"))))) (BDecls ([]))) ([]))))
-}

