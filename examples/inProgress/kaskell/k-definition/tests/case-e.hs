module CaseE where
  test1rhs = case v of { x@p -> e; _ -> e' }
  test1lhs = case v of { p -> ( \ x -> e ) v ; _ -> e' }

{-
 Parses as:

 (Module (SrcLoc "tests/case-e.hs" 1 1) (ModuleName "CaseE") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-e.hs" 2 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-e.hs" 2 26) (PAsPat (Ident "x") (PVar (Ident "p"))) (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-e.hs" 2 36) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-e.hs" 3 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-e.hs" 3 26) (PVar (Ident "p")) (UnGuardedAlt (App (Paren (Lambda (SrcLoc "tests/case-e.hs" 3 33) ((:)(PVar (Ident "x")) ([])) (Var (UnQual (Ident "e"))))) (Var (UnQual (Ident "v"))))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-e.hs" 3 48) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ([]))))

 After transformation:
  (Module (SrcLoc "tests/case-e.hs" 1 1) (ModuleName "CaseE") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-e.hs" 2 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-e.hs" 2 26) (PVar (Ident "p")) (UnGuardedAlt (App (Paren (Lambda (SrcLoc "tests/case-e.hs" 2 36) ((:)(PVar (Ident "x")) ([])) (Var (UnQual (UnQual (Ident "e")))))) (Var (UnQual (UnQual (Ident "v")))))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-e.hs" 2 36) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-e.hs" 3 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (App (Paren (Lambda (SrcLoc "tests/case-e.hs" 3 26) ((:)(PVar (Ident "p")) ([])) (App (Paren (Lambda (SrcLoc "tests/case-e.hs" 3 33) ((:)(PVar (Ident "x")) ([])) (Var (UnQual (Ident "e"))))) (Var (UnQual (Ident "v")))))) (Var (UnQual (Ident "v"))))) (BDecls ([]))) ([]))))



-}