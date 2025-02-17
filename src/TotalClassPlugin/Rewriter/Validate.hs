module TotalClassPlugin.Rewriter.Validate (checkNoPlaceholders) where

import Data.Foldable (forM_)

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Types (TcM)
import GHC.Tc.Types.Evidence (HsWrapper (..), TcEvBinds (TcEvBinds, EvBinds), EvBind (eb_rhs))
import GHC (HsBindLR (..), AbsBinds (..), LHsBind, HsBind, HsLocalBinds, HsLocalBindsLR (HsIPBinds), HsIPBinds (IPBinds), GhcTc, LHsExpr, HsExpr (XExpr), XXExprGhcTc (WrapExpr), HsWrap (HsWrap), LHsBinds)
import Data.Generics (everywhereM, mkM)
import TotalClassPlugin.Rewriter.Placeholder (isPlaceholder)
import GHC.Tc.Utils.Monad (wrapLocMA)

import TotalClassPlugin.Rewriter.Utils

checkNoPlaceholders :: LHsBinds GhcTc -> TcM ()
checkNoPlaceholders binds = do
  _ <- everywhereM (mkM checkDoneLHsBind) binds
  _ <- everywhereM (mkM checkDoneHsLocalBinds) binds
  _ <- everywhereM (mkM checkDoneLHsExpr) binds
  _ <- everywhereM (mkM (checkDoneTcEvBinds "Unknown TcEvBinds:")) binds
  return ()

checkDoneLHsBind :: LHsBind GhcTc -> TcM (LHsBind GhcTc)
checkDoneLHsBind = wrapLocMA checkDoneHsBind

checkDoneHsBind :: HsBind GhcTc -> TcM (HsBind GhcTc)
checkDoneHsBind xb@(XHsBindsLR (AbsBinds{abs_ev_binds=ev_binds})) = forM_ ev_binds (checkDoneTcEvBinds "AbsBinds:") >> return xb
checkDoneHsBind fb@(FunBind {fun_ext=(wrap, _)}) = checkDoneHsWrapper "FunBind wrapper:" wrap >> return fb
checkDoneHsBind b = return b

checkDoneLHsExpr :: LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
checkDoneLHsExpr = wrapLocMA checkDoneHsExpr

checkDoneHsExpr :: HsExpr GhcTc -> TcM (HsExpr GhcTc)
checkDoneHsExpr expr@(XExpr (WrapExpr (HsWrap wrap _))) = checkDoneHsWrapper "Expression wrapper:" wrap >> return expr
checkDoneHsExpr expr = return expr

checkDoneHsWrapper :: String -> HsWrapper -> TcM HsWrapper
checkDoneHsWrapper str (WpLet ev_binds) = WpLet <$> checkDoneTcEvBinds str ev_binds
checkDoneHsWrapper str (WpCompose w1 w2) = do
  w1' <- checkDoneHsWrapper str w1
  w2' <- checkDoneHsWrapper str w2
  return (WpCompose w1' w2')
checkDoneHsWrapper _ w = return w

checkDoneHsLocalBinds :: HsLocalBinds GhcTc -> TcM (HsLocalBinds GhcTc)
checkDoneHsLocalBinds lbs@(HsIPBinds _ (IPBinds ev_binds _)) = checkDoneTcEvBinds "HsIPBinds" ev_binds >> return lbs
checkDoneHsLocalBinds lbs = return lbs

checkDoneTcEvBinds :: String -> TcEvBinds -> TcM TcEvBinds
checkDoneTcEvBinds str (EvBinds binds)
  | any (isPlaceholder . eb_rhs) binds = failTcM $ text str <+> text "Found placeholder after rewrites: " <+> ppr binds
checkDoneTcEvBinds str (TcEvBinds _) = failTcM $ text str <+> text "Encountered unzonked TcEvBinds, this should not happen"
checkDoneTcEvBinds _ ev_binds = return ev_binds
