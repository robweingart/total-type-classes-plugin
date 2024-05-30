module TestPlugin.Placeholder (mkPlaceholder, isPlaceholder) where

import GHC.Plugins
import GHC.Tc.Types.Evidence (EvTerm (EvExpr))

placeholderString :: String
placeholderString = "Total type class placeholder instance"

mkPlaceholder :: PredType -> EvTerm
mkPlaceholder predType = if isPlaceholder expr then expr else error "isPlaceholder (mkPlaceholder _) is false, bug"
  where
    expr = EvExpr $ mkRuntimeErrorApp rUNTIME_ERROR_ID predType placeholderString

isPlaceholder :: EvTerm -> Bool
isPlaceholder (EvExpr (App (App (App _var _rep) _predtype) (Lit (LitString bs)))) = case mkLitString placeholderString of
  LitString bs' -> bs == bs'
  _ -> error "mkLitString did not return a LitString, this should be impossible"
isPlaceholder _ = False
