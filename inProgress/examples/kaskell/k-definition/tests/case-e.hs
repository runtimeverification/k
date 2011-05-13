module CaseE where
 test1rhs = case v of { x@P -> e; _ -> e' }
 test1lhs = case v of { P -> ( \ x -> e ) v ; _ -> e' }

{-
 Parses as:

 (Module (SrcLoc "tests/case-e.hs" 1 1) (ModuleName "CaseE") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-e.hs" 2 2) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-e.hs" 2 25) (PAsPat (Ident "x") (PApp (UnQual (Ident "P")) ([]))) (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-e.hs" 2 35) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-e.hs" 3 2) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-e.hs" 3 25) (PApp (UnQual (Ident "P")) ([])) (UnGuardedAlt (App (Paren (Lambda (SrcLoc "tests/case-e.hs" 3 32) ((:)(PVar (Ident "x")) ([])) (Var (UnQual (Ident "e"))))) (Var (UnQual (Ident "v"))))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-e.hs" 3 47) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ([]))))


 After transformation:

 (Module (SrcLoc "tests/case-e.hs" 1 1) (ModuleName "CaseE") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-e.hs" 2 2) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-e.hs" 2 25) (PApp (UnQual (Ident "P")) ([])) (UnGuardedAlt (App (Paren (Lambda (SrcLoc "tests/case-e.hs" 2 35) ((:)(PVar (Ident "x")) ([])) (Var (UnQual (Ident "e"))))) (Var (UnQual (UnQual (Ident "v")))))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-e.hs" 2 35) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-e.hs" 3 2) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-e.hs" 3 25) (PApp (UnQual (Ident "P")) ([])) (UnGuardedAlt (App (Paren (Lambda (SrcLoc "tests/case-e.hs" 3 32) ((:)(PVar (Ident "x")) ([])) (Var (UnQual (Ident "e"))))) (Var (UnQual (Ident "v"))))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-e.hs" 3 47) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ([]))))


-}