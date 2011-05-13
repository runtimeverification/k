module CaseP where
  data K = K Int Int Int
  data K' = K' Int Int Int
  test1lhs = case (K' 1 2 3) of { K x1 x2 x3 -> e; _ -> e' }
  test1rhs = e'

{-
  Parses as

  (Module (SrcLoc "tests/case-p.hs" 1 1) (ModuleName "CaseP") ([]) Nothing Nothing ([]) ((:)(DataDecl (SrcLoc "tests/case-p.hs" 2 3) DataType ([]) (Ident "K") ([]) ((:)(QualConDecl (SrcLoc "tests/case-p.hs" 2 12) ([]) ([]) (ConDecl (Ident "K") ((:)(UnBangedTy (TyCon (UnQual (Ident "Int")))) ((:)(UnBangedTy (TyCon (UnQual (Ident "Int")))) ((:)(UnBangedTy (TyCon (UnQual (Ident "Int")))) ([])))))) ([])) ([])) ((:)(DataDecl (SrcLoc "tests/case-p.hs" 3 3) DataType ([]) (Ident "K'") ([]) ((:)(QualConDecl (SrcLoc "tests/case-p.hs" 3 13) ([]) ([]) (ConDecl (Ident "K'") ((:)(UnBangedTy (TyCon (UnQual (Ident "Int")))) ((:)(UnBangedTy (TyCon (UnQual (Ident "Int")))) ((:)(UnBangedTy (TyCon (UnQual (Ident "Int")))) ([])))))) ([])) ([])) ((:)(PatBind (SrcLoc "tests/case-p.hs" 4 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Case (Paren (App (App (App (Con (UnQual (Ident "K'"))) (Lit (Int 1))) (Lit (Int 2))) (Lit (Int 3)))) ((:)(Alt (SrcLoc "tests/case-p.hs" 4 35) (PApp (UnQual (Ident "K")) ((:)(PVar (Ident "x1")) ((:)(PVar (Ident "x2")) ((:)(PVar (Ident "x3")) ([]))))) (UnGuardedAlt (Var (UnQual (Ident "e")))) (BDecls ([]))) ((:)(Alt (SrcLoc "tests/case-p.hs" 4 52) PWildCard (UnGuardedAlt (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-p.hs" 5 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))))

  After transformation:
 (Module (SrcLoc "tests/case-p.hs" 1 1) (ModuleName "CaseP") ([]) Nothing Nothing ([]) ((:)(DataDecl (SrcLoc "tests/case-p.hs" 2 3) DataType ([]) (Ident "K") ([]) ((:)(QualConDecl (SrcLoc "tests/case-p.hs" 2 12) ([]) ([]) (ConDecl (Ident "K") ((:)(UnBangedTy (TyCon (UnQual (Ident "Int")))) ((:)(UnBangedTy (TyCon (UnQual (Ident "Int")))) ((:)(UnBangedTy (TyCon (UnQual (Ident "Int")))) ([])))))) ([])) ([])) ((:)(DataDecl (SrcLoc "tests/case-p.hs" 3 3) DataType ([]) (Ident "K'") ([]) ((:)(QualConDecl (SrcLoc "tests/case-p.hs" 3 13) ([]) ([]) (ConDecl (Ident "K'") ((:)(UnBangedTy (TyCon (UnQual (Ident "Int")))) ((:)(UnBangedTy (TyCon (UnQual (Ident "Int")))) ((:)(UnBangedTy (TyCon (UnQual (Ident "Int")))) ([])))))) ([])) ([])) ((:)(PatBind (SrcLoc "tests/case-p.hs" 4 3) (PVar (Ident "test1lhs")) Nothing (UnGuardedRhs (Var (UnQual (Ident "e'")))) (BDecls ([]))) ((:)(PatBind (SrcLoc "tests/case-p.hs" 5 3) (PVar (Ident "test1rhs")) Nothing (UnGuardedRhs (Var (UnQual (Ident "e'")))) (BDecls ([]))) ([]))))))


-}
