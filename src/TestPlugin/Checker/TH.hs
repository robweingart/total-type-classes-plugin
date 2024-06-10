{-# LANGUAGE TemplateHaskell #-}

module TestPlugin.Checker.TH ( mkEvidenceFun ) where

import Language.Haskell.TH

mkEvidenceFun :: Name -> [Bool] -> Q [Dec]
mkEvidenceFun name match_on = do
  let args = VarT . mkName . ("a" ++) . show <$> [1..length match_on]
  ty <- reifyType name
  insts <- reifyInstances name args
  clauses <- mapM (mkInstClause match_on) insts
  let fun_name = mkName ("evidenceFun" ++ nameBase name)
  fun_type <- mk_type match_on ty
  return [SigD fun_name fun_type, FunD fun_name clauses]
  where
    unit_type = [t| () |]
   
    unit_unless True x = return x
    unit_unless False _ = unit_type

    mk_type bs (ForallT bndrs [] ty') = ForallT bndrs [] <$> mk_type bs ty'
    mk_type bs (ForallVisT bndrs ty') = ForallVisT bndrs <$> mk_type bs ty'
    mk_type (b : bs) (AppT (AppT f x) y)
      | ArrowT <- f = do 
        x' <- unit_unless b x
        y' <- mk_type bs y
        return $ (AppT (AppT f x') y')
      | MulArrowT <- f = do
        x' <- unit_unless b x
        y' <- mk_type bs y
        return $ (AppT (AppT f x') y')
    mk_type [] ConstraintT = unit_type
    mk_type _ _ = fail "invalid class constructor type"

mkInstClause :: [Bool] -> InstanceDec -> Q Clause
mkInstClause match_on (InstanceD _ _ t _) = do
  let args = get_args t []
  pats <- demoteToPats match_on args
  body <- [| () |]
  return $ Clause pats (NormalB body) []
  where
    get_args (AppT f x) args = get_args f (x : args) 
    get_args _ args = args
mkInstClause _ _ = fail "Not an instance"

demoteToPats :: [Bool] -> [Type] -> Q [Pat]
demoteToPats [] [] = return []
demoteToPats (True : bs) (t : ts) = liftA2 (:) (demoteToPat t) (demoteToPats bs ts)
demoteToPats (False : bs) (_ : ts) = (WildP :) <$> demoteToPats bs ts
demoteToPats _ _ = fail "wrong arity"

demoteToPat :: Type -> Q Pat
demoteToPat t = go t []
  where
    go :: Type -> [Q Pat] -> Q Pat
    go (VarT _) [] = wildP
    go (AppT f x) args = go f (demoteToPat x : args)
    go (PromotedT name) args = conP name args
    go (PromotedInfixT t1 name t2) [] =  do
      p1 <- demoteToPat t1
      p2 <- demoteToPat t2
      return $ InfixP p1 name p2
    go (ParensT t') args = go t' args
    go (PromotedTupleT _) args = tupP args 
    go (PromotedNilT) [] = listP []
    go (PromotedConsT) [p, ps] = do
      ListP ps' <- ps
      listP (p : map return ps')
    go (LitT (NumTyLit n)) [] = litP (IntegerL n)
    go (LitT (StrTyLit s)) [] = litP (StringL s)
    go (LitT (CharTyLit c)) [] = litP (CharL c)
    go ty args = do 
      args' <- sequence args 
      fail $ "Invalid: " ++ show ty ++ " with args " ++ show args'

