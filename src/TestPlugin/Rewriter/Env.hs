module TestPlugin.Rewriter.Env (UpdateInfo(..), UpdateEnv) where

import GHC.Plugins
import GHC.Tc.Utils.TcType (TcThetaType)

data UpdateInfo = UInfo { old_type :: Type, new_id :: Id, new_theta :: TcThetaType, last_ty_var :: TyVar }

type UpdateEnv = DNameEnv UpdateInfo
