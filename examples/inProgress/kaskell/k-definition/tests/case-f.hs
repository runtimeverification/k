module CaseF where
  test1rhs = case v of { _ -> e; _ -> e' }
  test1lhs = e

{-
 Parses as:

 (Module (SrcLoc "tests/case-f.hs" 1 1) (ModuleName "CaseF") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-f.hs" 2 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-f.hs" 2 26) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-f.hs" 2 34) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-f.hs" 3 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Var (UnQual (Ident "e")))) (BDecls ([]))) ([]))))


 After transformation:
 (Module (SrcLoc "tests/case-f.hs" 1 1) (ModuleName "CaseF") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-f.hs" 2 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Var (UnQual (Ident "e")))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-f.hs" 3 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Var (UnQual (Ident "e")))) (BDecls ([]))) ([]))))



-}