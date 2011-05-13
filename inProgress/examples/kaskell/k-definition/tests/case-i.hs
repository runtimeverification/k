module CaseI where
  test1lhs = case v of { x -> e; _ -> e' }
  test1rhs = case v of { x -> e }

{-
 Parses as:

 (Module (SrcLoc "tests/case-i.hs" 1 1) (ModuleName "Case") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-i.hs" 2 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-i.hs" 2 26) (PVar (Ident "x")) (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-i.hs" 2 34) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-i.hs" 3 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-i.hs" 3 26) (PVar (Ident "x")) (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ([])))) (BDecls ([]))) ([]))))

 After transformation:
(Module (SrcLoc "tests/case-i.hs" 1 1) (ModuleName "CaseI") ([]) Nothing Nothing ([]) ((:)(PatBind (SrcLoc "tests/case-i.hs" 2 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-i.hs" 2 26) (PVar (Ident "x")) (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ([])))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-i.hs" 3 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Case (Var (UnQual (Ident "v"))) ((:)(Alt (SrcLoc "tests/case-i.hs" 3 26) (PVar (Ident "x")) (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ([])))) (BDecls ([]))) ([]))))

-}