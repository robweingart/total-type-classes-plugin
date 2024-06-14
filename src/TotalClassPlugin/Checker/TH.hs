{-# LANGUAGE TemplateHaskell #-}

module TotalClassPlugin.Checker.TH ( mkEvidenceFun ) where

import Language.Haskell.TH
import GHC.Tc.Utils.Monad (TcM)
import GHC.Plugins (CoreExpr)
import GHC.Tc.Gen.Splice (runQuasi)
import GHC.HsToCore.Expr (dsExpr)
import GHC.ThToHs (convertToHsExpr)

mkEvidenceFun :: Name -> Int -> Q [Dec]
mkEvidenceFun name arity = do
  let args = VarT . mkName . ("a" ++) . show <$> [1..arity]
  --ty <- reifyType name
  
  insts <- reifyInstances name args
  clauses <- mapM mkInstClause insts
  let fun_name = mkName ("evidenceFun" ++ nameBase name)
  --fun_type <- mk_type ty
  return [FunD fun_name clauses]
  --where
    --unit_type = [t| () |]

    --mk_type (ForallT bndrs [] ty') = ForallT bndrs [] <$> mk_type ty'
    --mk_type (ForallVisT bndrs ty') = ForallVisT bndrs <$> mk_type ty'
    --mk_type (AppT (AppT f x) y)
    --  | ArrowT <- f = do 
    --    x' <- demoteArgType x
    --    y' <- mk_type y
    --    return $ (AppT (AppT f x') y')
    --  | MulArrowT <- f = do
    --    x' <- demoteArgType x
    --    y' <- mk_type y
    --    return $ (AppT (AppT f x') y')
    --mk_type ConstraintT = unit_type
    --mk_type _ = fail "invalid class constructor type"

--demoteArgType :: Type -> Q Type
--demoteArgType ty = go ty []
--  where
--    go (VarT name) [] = return $ VarT name
--    go (AppT f x) args = go f (demoteArgType x : args)
--    go (PromotedT name) args = return $ ConT

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
