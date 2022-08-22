{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}

#if __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
#endif

#include "ghc-compat.h"

{-
This seems to work. But it is a hack!
A 10-line patch extending the GHC-API would make that go away
-}

module HsToCoq.Util.GHC.Deriving (initForDeriving, addDerivedInstances) where

import GHC

import Control.Monad

import GHC.IO (throwIO)
#if __GLASGOW_HASKELL__ < 900
#if __GLASGOW_HASKELL__ >= 808
import GhcPlugins (SourceText(NoSourceText), PromotionFlag(NotPromoted))
#else
import GhcPlugins (SourceText(NoSourceText))
#endif
import Outputable
import TcRnMonad
import TcEnv
import InstEnv
import Var
import TyCoRep
import TyCon
import Type
import TcType
import HscTypes
import TcInstDcls
import Module
import SrcLoc
import FastString
import DynFlags
#else
import GHC.Plugins as Type
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.Env
import GHC.Tc.Utils.TcType
import GHC.Tc.TyCl.Instance (tcInstDeclsDeriv)
import GHC.Types.SourceFile (HscSource(HsSrcFile))
import GHC.Types.SourceText (SourceText(NoSourceText))
import GHC.Core.TyCo.Rep
import GHC.Core.InstEnv (instanceSig)
import GHC.Driver.Errors.Types (GhcMessage(GhcTcRnMessage))
#endif
import qualified GHC.LanguageExtensions as LangExt

-- We need to allow IncoherentInstances for the hack in HsToCoq.Util.GHC.Deriving
initForDeriving :: GhcMonad m => m ()
initForDeriving =
  void $ getSessionDynFlags >>= setSessionDynFlags . (`xopt_set` LangExt.IncoherentInstances)

addDerivedInstances :: GhcMonad m => TypecheckedModule -> m TypecheckedModule
addDerivedInstances tcm = do
    let Just (hsgroup, a, b, c) = tm_renamed_source tcm

    (_gbl_env, inst_infos, _rn_binds) <- initTcHack tcm $ do
        let tcg_env = fst (tm_internals_ tcm)
            tcg_env_hack = tcg_env { tcg_mod = fakeDerivingMod, tcg_semantic_mod = fakeDerivingMod }
                -- Set the module to make it look like we are in GHCi
                -- so that GHC will allow us to re-typecheck existing instances
        setGblEnv tcg_env_hack $
#if __GLASGOW_HASKELL__ >= 810
            tcInstDeclsDeriv [] (hs_derivds hsgroup)
#else
            tcInstDeclsDeriv [] (hs_tyclds hsgroup >>= group_tyclds) (hs_derivds hsgroup)
#endif

    let inst_decls = map instInfoToDecl $ inst_infos

#if __GLASGOW_HASKELL__ >= 806
    let mkTyClGroup decls instds = TyClGroup
          { group_ext = NOEXT
          , group_tyclds = decls
          , group_roles = []
#if __GLASGOW_HASKELL__ >= 810
          , group_kisigs = []
#endif
          , group_instds = instds
          }
#endif
    let hsgroup' = hsgroup { hs_tyclds = mkTyClGroup [] inst_decls : hs_tyclds hsgroup }

    return $ tcm { tm_renamed_source = Just (hsgroup', a, b, c) }

initTcHack :: GhcMonad m => TypecheckedModule -> TcM a -> m a
initTcHack tcm action = do
 hsc_env <- getSession
 let hsc_env_tmp = hsc_env
        { hsc_dflags = ms_hspp_opts (pm_mod_summary (tm_parsed_module tcm)) }
 let mod = fakeDerivingMod
 -- let mod = icInteractiveModule (hsc_IC hsc_env)
 let src_span = realSrcLocSpan (mkRealSrcLoc (fsLit "<deriving>") 1 1)

 (msgs, mba) <- liftIO $ initTc hsc_env_tmp HsSrcFile False mod src_span action
 case mba of Just x ->  return x
             Nothing -> liftIO $ throwIO $ mkSrcErr $
#if __GLASGOW_HASKELL__ >= 900
               fmap GhcTcRnMessage msgs
#else
               snd msgs
#endif

fakeDerivingMod :: Module
fakeDerivingMod = mkModule
#if __GLASGOW_HASKELL__ >= 900
  interactiveUnit
#else
  interactiveUnitId
#endif
  (mkModuleName "Deriving")


instInfoToDecl :: InstInfo GhcRn -> LInstDecl GhcRn
instInfoToDecl inst_info =
#if __GLASGOW_HASKELL__ >= 900
  noLocA
#else
  noLoc
#endif
    $ ClsInstD NOEXT (ClsInstDecl
    { cid_binds = ib_binds (iBinds inst_info)
    , cid_sigs = []
    , cid_tyfam_insts = []
    , cid_datafam_insts = []
    , cid_overlap_mode = Nothing
#if __GLASGOW_HASKELL__ >= 900
    , cid_poly_ty = noLocA $ HsSig NOEXT (HsOuterImplicit tvars_) $ noLocA $ HsQualTy NOEXT (noLocA ctxt) inst_head
#elif __GLASGOW_HASKELL__ >= 808
    , cid_poly_ty = HsIB @GhcRn tvars_ (noLoc (HsQualTy NOEXT (noLoc ctxt) inst_head))
#elif __GLASGOW_HASKELL__ == 806
    , cid_poly_ty = HsIB @GhcRn (HsIBRn tvars_ True) (noLoc (HsQualTy NOEXT (noLoc ctxt) inst_head))
#else
    , cid_poly_ty = HsIB tvars_ (noLoc (HsQualTy (noLoc ctxt) inst_head)) True
#endif
#if __GLASGOW_HASKELL__ >= 806
    , cid_ext = NOEXT
#endif
    })
  where
    (tvars, theta, cls, args) = instanceSig (iSpec inst_info)
    tvars_ :: [Name]
    tvars_ = map tyVarName tvars
    ctxt = map typeToLHsType' theta
    inst_head = foldl lHsAppTy (noLocA (HsTyVar noAnn NotPromoted (noLocA (getName cls)))) $
        map typeToLHsType' args

    lHsAppTy f x = noLocA (HsAppTy NOEXT f x)

#if __GLASGOW_HASKELL__ >= 900
#define noLoc noLocA
#endif

-- Taken from HsUtils. We need it to produce a Name, not a RdrName
typeToLHsType' :: Type -> LHsType GhcRn
typeToLHsType' ty
  = go ty
  where
    go :: Type -> LHsType GhcRn
    go ty@(FunTy {})
#if __GLASGOW_HASKELL__ >= 900
      | (_, arg, res) <- splitFunTy ty =
#else
      | (arg, res) <- splitFunTy ty =
#endif
      if isPredTy arg then
        let (theta, tau) = tcSplitPhiTy ty in
        noLoc (HsQualTy { hst_ctxt = noLoc (map go theta)
                        , hst_body = go tau
#if __GLASGOW_HASKELL__ >= 806
                        , hst_xqual = NOEXT
#endif
                        })
      else nlHsFunTy (go arg) (go res)
    go ty@(ForAllTy {})
#if __GLASGOW_HASKELL__ >= 900
      | (tvs, tau) <- tcSplitForAllTyVars ty
#else
      | (tvs, tau) <- tcSplitForAllTys ty
#endif
      = noLoc (HsForAllTy {
#if __GLASGOW_HASKELL__ >= 900
                            hst_tele = HsForAllInvis noAnn (map go_tv tvs)
#else
                            hst_bndrs = map go_tv tvs
#if __GLASGOW_HASKELL__ >= 810
                          , hst_fvf = ForallInvis
#endif
#endif
                          , hst_body = go tau
#if __GLASGOW_HASKELL__ >= 806
                          , hst_xforall = NOEXT
#endif
                          })
#if __GLASGOW_HASKELL__ >= 900
    go (TyVarTy tv)         = nlHsTyVar NotPromoted (getName tv)
#else
    go (TyVarTy tv)         = nlHsTyVar (getName tv)
#endif
    go (AppTy t1 t2)        = nlHsAppTy (go t1) (go t2)
    go (LitTy (NumTyLit n)) = noLoc $ HsTyLit NOEXT (HsNumTy NoSourceText n)
    go (LitTy (StrTyLit s)) = noLoc $ HsTyLit NOEXT (HsStrTy NoSourceText s)
    go ty@(TyConApp tc args)
      | any isInvisibleTyConBinder (tyConBinders tc)
        -- We must produce an explicit kind signature here to make certain
        -- programs kind-check. See Note [Kind signatures in typeToLHsType].
#if __GLASGOW_HASKELL__ >= 900
      = noLocA $ HsKindSig noAnn lhs_ty (go (Type.typeKind ty))
#else
      = noLoc $ HsKindSig NOEXT lhs_ty (go (Type.typeKind ty))
#endif
      | otherwise = lhs_ty
       where
        lhs_ty = nlHsTyConApp
#if __GLASGOW_HASKELL__ >= 900
          NotPromoted Prefix (getName tc) (map (HsValArg . go) args')
#else
          (getName tc) (map go args')
#endif
        args'  = filterOutInvisibleTypes tc args
    go (CastTy ty _)        = go ty
    go (CoercionTy co)      = pprPanic "toLHsSigWcType" (ppr co)

         -- Source-language types have _invisible_ kind arguments,
         -- so we must remove them here (Trac #8563)

    go_tv :: TyVar -> LHsTyVarBndr
#if __GLASGOW_HASKELL__ >= 900
      Specificity
#endif
      GhcRn
    go_tv tv = noLoc $ KindedTyVar
#if __GLASGOW_HASKELL__ >= 900
        noAnn InferredSpec
#else
        NOEXT
#endif
        (noLoc (getName tv)) (go (tyVarKind tv))

