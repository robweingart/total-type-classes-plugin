module TestPlugin.Rewriter.Env (UpdateInfo(..), UpdateEnv) where

import GHC.Plugins
import GHC.Tc.Utils.TcType (TcThetaType)

data UpdateInfo = UInfo { old_type :: Type, new_id :: Id, new_theta :: TcThetaType, last_ty_var :: TyVar }

instance Outputable UpdateInfo where
  ppr u = text "Update:" <+> (vcat $
    [ text "Id:" <+> ppr (new_id u)
    , text "Old type:" <+> ppr (old_type u)
    , text "New type:" <+> ppr (idType (new_id u))
    , text "New theta:" <+> ppr (new_theta u)
    , text "Unique of last ty var binder:" <+> ppr (varUnique (last_ty_var u))
    ])

type UpdateEnv = DNameEnv UpdateInfo
