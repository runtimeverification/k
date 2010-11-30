module CaseJ where
  test1lhs = case v of { x -> e }
  test1rhs = ( \x -> e ) v

{-
 Parses as:
 (Module (SrcLoc "tests/case-j.hs" 1 1) (ModuleName "CaseJ") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-j.hs" 2 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-j.hs" 2 26) (PVar (Ident "x")) (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ([])))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-j.hs" 3 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (App (Paren (Lambda (SrcLoc "tests/case-j.hs" 3 16) ((:)(PVar (Ident "x")) ([])) (Var (UnQual (Ident "e"))))) (Var (UnQual (Ident "v"))))) (BDecls ([]))) ([]))))

 After transformation:
 (Module (SrcLoc "tests/case-j.hs" 1 1) (ModuleName "CaseJ") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-j.hs" 2 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (App (Paren (Lambda (SrcLoc "tests/case-j.hs" 2 26) ((:)(PVar (Ident "x")) ([])) (Var (UnQual (Ident "e"))))) (Var (UnQual (Ident "v"))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-j.hs" 3 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (App (Paren (Lambda (SrcLoc "tests/case-j.hs" 3 16) ((:)(PVar (Ident "x")) ([])) (Var (UnQual (Ident "e"))))) (Var (UnQual (Ident "v"))))) (BDecls ([]))) ([]))))


-}