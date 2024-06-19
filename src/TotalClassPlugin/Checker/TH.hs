{-# LANGUAGE TemplateHaskell #-}

module TotalClassPlugin.Checker.TH ( mkEvidenceFun ) where

import Language.Haskell.TH

mkEvidenceFun :: Name -> Int -> Q [Dec]
mkEvidenceFun name arity = do
  let args = VarT . mkName . ("a" ++) . show <$> [1..arity]
  insts <- reifyInstances name args
  clauses <- mapM mkInstClause insts
  let fun_name = mkName ("evidenceFun" ++ nameBase name)
  return [FunD fun_name clauses]

mkInstClause :: InstanceDec -> Q Clause
mkInstClause (InstanceD _ _ t _) = do
  let args = get_args t []
  pats <- demoteToPats args
  body <- [| () |]
  return $ Clause pats (NormalB body) []
  where
    get_args (AppT f x) args = get_args f (x : args) 
    get_args _ args = args
mkInstClause _ = fail "Not an instance"

demoteToPats :: [Type] -> Q [Pat]
demoteToPats ts = mapM demoteToPat ts

demoteToPat :: Type -> Q Pat
demoteToPat t = go t []
  where
    go :: Type -> [Q Pat] -> Q Pat
    go (VarT _) [] = wildP
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
