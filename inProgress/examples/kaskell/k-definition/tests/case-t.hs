{-# LANGUAGE PatternGuards #-}
module CaseT where
-- I use a constructor for the pattern, so that case (i) doesn't apply.
  test1lhs = case () of { () | Pat pat <- e0 -> e; _ -> e' }
  test1rhs = case e0 of { Pat pat -> e; _ -> e' }



{-
  Parses as:

 (Module (SrcLoc "tests/case-t.hs" 1 1) (ModuleName "CaseT") ((:)(LanguagePragma (SrcLoc "tests/case-t.hs" 1 1) ((:)(Ident "PatternGuards") ([]))) ([])) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-t.hs" 4 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Case (Con (Special UnitCon)) ((:)(Alt (SrcLoc "tests/case-t.hs" 4 27) (PApp (Special UnitCon) ([])) (GuardedAlts ((:)(GuardedAlt (SrcLoc "tests/case-t.hs" 4 30) ((:)(Generator (SrcLoc "tests/case-t.hs" 4 32) (PApp (UnQual (Ident "Pat")) ((:)(PVar (Ident "pat")) ([]))) (Var (UnQual (Ident "e0")))) ([])) (Var (UnQual (Ident "e")))) ([]))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-t.hs" 4 52) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-t.hs" 5 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "e0"))) ((:)(Alt (SrcLoc "tests/case-t.hs" 5 27) (PApp (UnQual (Ident "Pat")) ((:)(PVar (Ident "pat")) ([]))) (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-t.hs" 5 41) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ([]))))

  After transformation:

 (Module (SrcLoc "tests/case-t.hs" 1 1) (ModuleName "CaseT") ((:)(LanguagePragma (SrcLoc "tests/case-t.hs" 1 1) ((:)(Ident "PatternGuards") ([]))) ([])) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-t.hs" 4 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "e0"))) ((:)(Alt (SrcLoc "tests/case-t.hs" 4 27) (PApp (UnQual (Ident "Pat")) ((:)(PVar (Ident "pat")) ([]))) (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-t.hs" 4 52) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-t.hs" 5 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "e0"))) ((:)(Alt (SrcLoc "tests/case-t.hs" 5 27) (PApp (UnQual (Ident "Pat")) ((:)(PVar (Ident "pat")) ([]))) (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-t.hs" 5 41) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ([]))))


 -}
