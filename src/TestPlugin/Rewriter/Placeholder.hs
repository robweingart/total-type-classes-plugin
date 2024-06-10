module TestPlugin.Rewriter.Placeholder (mkPlaceholder, isPlaceholder, getPlaceholderPredType) where

import GHC.Plugins
import GHC.Tc.Types.Evidence (EvTerm (EvExpr))
import Data.ByteString (ByteString)
import Data.Maybe (isJust)

placeholderString :: String
placeholderString = "Total type class placeholder instance"

placeholderBS :: ByteString
placeholderBS = case mkLitString placeholderString of
  LitString bs -> bs
  _ -> error "mkLitString did not return a LitString, this should be impossible"


mkPlaceholder :: PredType -> EvTerm
mkPlaceholder predType = if isPlaceholder expr then expr else error "isPlaceholder (mkPlaceholder _) is false, bug"
  where
    expr = EvExpr $ mkImpossibleExpr predType placeholderString

isPlaceholder :: EvTerm -> Bool
isPlaceholder = isJust . getPlaceholderPredType

getPlaceholderPredType :: EvTerm -> Maybe PredType 
getPlaceholderPredType (EvExpr (App (App (App (Var _id) (Type _rep)) (Type predType)) (Lit (LitString bs)))) = if bs == placeholderBS then Just predType else Nothing
getPlaceholderPredType _ = Nothing
  
