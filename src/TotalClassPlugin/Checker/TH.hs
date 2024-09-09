{-# LANGUAGE TemplateHaskell #-}

module TotalClassPlugin.Checker.TH ( mkEvidenceFun ) where

import Language.Haskell.TH

mkEvidenceFun :: [[Type]] -> Q [Dec]
mkEvidenceFun pat_types = do
  clauses <- mapM mk_inst pat_types
  return [FunD (mkName "evidenceFun") clauses]

mk_inst :: [Type] -> Q Clause
mk_inst pat_types = do
  pats <- demoteToPats pat_types
  body <- [| () |]
  return $ Clause pats (NormalB body) []

demoteToPats :: [Type] -> Q [Pat]
demoteToPats ts = mapM demoteToPat ts

demoteToPat :: Type -> Q Pat
demoteToPat t = go t []
  where
    go :: Type -> [Q Pat] -> Q Pat
    go (VarT name) [] = varP (mkName (nameBase name))
    go (AppT f x) args = go f (demoteToPat x : args)
    go (SigT ty _) args = go ty args
    go (PromotedT name) args = conP name args
    go (PromotedInfixT t1 name t2) [] =  do
      p1 <- demoteToPat t1
      p2 <- demoteToPat t2
      return $ InfixP p1 name p2
    go (ParensT t') args = go t' args
    go (PromotedTupleT _) args = tupP args 
    go (PromotedNilT) [] = listP []
    go (PromotedConsT) args = conP '(:) args
    go (LitT (NumTyLit n)) [] = litP (IntegerL n)
    go (LitT (StrTyLit s)) [] = litP (StringL s)
    go (LitT (CharTyLit c)) [] = litP (CharL c)
    go ty _ = fail $ "Invalid type: " ++ show ty
