{-# LANGUAGE PatternGuards #-}
module CaseU where
  test1lhs = case () of { () | let x1 = a -> e; _ -> e' }
  test1rhs = let x1 = a in e

{-
  Parses as:

(Module (SrcLoc "tests/case-u.hs" 1 1) (ModuleName "CaseU") ((:)(LanguagePragma (SrcLoc "tests/case-u.hs" 1 1) ((:)(Ident "PatternGuards") ([]))) ([])) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-u.hs" 3 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Case (Con (Special UnitCon)) ((:)(Alt (SrcLoc "tests/case-u.hs" 3 27) (PApp (Special UnitCon) ([])) (GuardedAlts ((:)(GuardedAlt (SrcLoc "tests/case-u.hs" 3 30) ((:)(LetStmt (BDecls ((:)(PatBind (SrcLoc "tests/case-u.hs" 3 36) (PVar (Ident "x1")) Nothing (UnGuardedRhs (Var (UnQual (Ident "a")))) (BDecls ([]))) ([])))) ([])) (Var (UnQual (Ident "e")))) ([]))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-u.hs" 3 49) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-u.hs" 4 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Let (BDecls ((:)(PatBind (SrcLoc "tests/case-u.hs" 4 18) (PVar (Ident "x1")) Nothing (UnGuardedRhs (Var (UnQual (Ident "a")))) (BDecls ([]))) ([]))) (Var (UnQual (Ident "e"))))) (BDecls ([]))) ([]))))

 After transformation:

 (Module (SrcLoc "tests/case-u.hs" 1 1) (ModuleName "CaseU") ((:)(LanguagePragma (SrcLoc "tests/case-u.hs" 1 1) ((:)(Ident "PatternGuards") ([]))) ([])) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-u.hs" 3 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Let (BDecls ((:)(PatBind (SrcLoc "tests/case-u.hs" 3 36) (PVar (Ident "x1")) Nothing (UnGuardedRhs (Var (UnQual (Ident "a")))) (BDecls ([]))) ([]))) (Var (UnQual (Ident "e"))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-u.hs" 4 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Let (BDecls ((:)(PatBind (SrcLoc "tests/case-u.hs" 4 18) (PVar (Ident "x1")) Nothing (UnGuardedRhs (Var (UnQual (Ident "a")))) (BDecls ([]))) ([]))) (Var (UnQual (Ident "e"))))) (BDecls ([]))) ([]))))

-}
