module TotalClassPlugin.Rewriter.Env (UpdateInfo(..), UpdateEnv, updateInfoNewType, updateInfoNewTheta, updateInfoLastTyVar, extendGlobalEnvWithUpdates, updateInfoCtOrigin) where

import GHC.Plugins
import GHC.Tc.Utils.TcType (TcThetaType)
import GHC.Tc.Types.Origin (CtOrigin (OccurrenceOf))
import GHC.Tc.Utils.Env (tcExtendGlobalEnv, TyThing (AnId))
import Data.Foldable (Foldable(toList))
import TotalClassPlugin.Rewriter.Utils (failTcM)
import GHC.Tc.Types (TcM)

data UpdateInfo = IdUpdate { old_type :: Type, new_id :: Id, new_theta :: TcThetaType, last_ty_var :: TyVar }
                | InlineUpdate { origin :: CtOrigin, new_type :: Type, new_theta :: TcThetaType, last_ty_var :: TyVar }

updateInfoNewType :: UpdateInfo -> Kind
updateInfoNewType IdUpdate{new_id=updated_id} = idType updated_id
updateInfoNewType InlineUpdate{new_type=ty} = ty

updateInfoNewTheta :: UpdateInfo -> TcThetaType
updateInfoNewTheta IdUpdate{new_theta=theta} = theta
updateInfoNewTheta InlineUpdate{new_theta=theta} = theta

updateInfoLastTyVar :: UpdateInfo -> TyVar
updateInfoLastTyVar IdUpdate{last_ty_var=tv} = tv
updateInfoLastTyVar InlineUpdate{last_ty_var=tv} = tv

updateInfoCtOrigin :: UpdateInfo -> CtOrigin
updateInfoCtOrigin IdUpdate{new_id=updated_id} = OccurrenceOf (idName updated_id)
updateInfoCtOrigin InlineUpdate{origin=orig} = orig

instance Outputable UpdateInfo where
  ppr u = text "Update:" <+> (vcat $
    [ text "Old type:" <+> ppr (old_type u)
    , text "New type:" <+> ppr (new_type u)
    , text "New theta:" <+> ppr (new_theta u)
    , text "Unique of last ty var binder:" <+> ppr (varUnique (last_ty_var u))
    ])

type UpdateEnv = DNameEnv UpdateInfo

updateInfoNewId :: UpdateInfo -> TcM Id
updateInfoNewId IdUpdate{new_id=updated_id} = return updated_id
updateInfoNewId InlineUpdate{} = failTcM $ text "can't add inline update to environment"

extendGlobalEnvWithUpdates :: UpdateEnv -> TcM r -> TcM r
extendGlobalEnvWithUpdates updates thing_inside = do
  things <- mapM updateInfoNewId (toList updates)
  tcExtendGlobalEnv (map AnId things) thing_inside
