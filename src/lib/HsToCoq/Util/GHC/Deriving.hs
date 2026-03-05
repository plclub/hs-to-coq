{-# LANGUAGE CPP #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

#if __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
#endif

#include "ghc-compat.h"

{-
This seems to work. But it is a hack!
A 10-line patch extending the GHC-API would make that go away
-}

module HsToCoq.Util.GHC.Deriving (initForDeriving, addDerivedInstances, DerivSkipInfo(..)) where

import GHC

import Control.Monad
import Data.Maybe (catMaybes, mapMaybe)
import qualified Data.Set as S
import qualified Data.Text as T

#if __GLASGOW_HASKELL__ >= 900
import GHC.Plugins
import GHC.Parser.Annotation (noAnn)
import GHC.Types.SourceText
#elif __GLASGOW_HASKELL__ >= 808
import GhcPlugins (SourceText(NoSourceText), PromotionFlag(NotPromoted))
#else
import GhcPlugins (SourceText(NoSourceText))
#endif

import Control.Monad

import GHC.IO (throwIO)
import qualified Control.Exception as E
#if __GLASGOW_HASKELL__ >= 902
import GHC.Utils.Outputable
import GHC.Driver.Session
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.Env
import GHC.Tc.Utils.TcType
import GHC.Tc.TyCl (tcTyAndClassDecls)
import GHC.Tc.TyCl.Instance (tcInstDeclsDeriv)
import GHC.Types.SourceFile (HscSource(HsSrcFile))
import GHC.Types.SourceText (SourceText(NoSourceText))
import GHC.Types.Var
import GHC.Types.Error
import GHC.Driver.Errors.Types (GhcMessage(GhcTcRnMessage))
import GHC.Core.Type as Type
import GHC.Core.TyCo.Rep
import GHC.Core.InstEnv (instanceSig)
#else
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
#if __GLASGOW_HASKELL__ >= 810
import TcTyClsDecls
#endif
import Module
import SrcLoc
import FastString
import DynFlags
#endif
import qualified GHC.LanguageExtensions as LangExt

-- We need to allow IncoherentInstances for the hack in HsToCoq.Util.GHC.Deriving
initForDeriving :: GhcMonad m => m ()
initForDeriving =
  void $ getSessionDynFlags >>= setSessionDynFlags . (`xopt_set` LangExt.IncoherentInstances)

data DerivSkipInfo = DerivSkipInfo
  { dsi_skippedModules :: S.Set T.Text
  , dsi_skippedClasses :: S.Set T.Text
  }

#if __GLASGOW_HASKELL__ >= 910
-- | Check if a Name belongs to a skipped module
nameInSkippedModule :: DerivSkipInfo -> Name -> Bool
nameInSkippedModule dsi name =
  case nameModule_maybe name of
    Just m  -> T.pack (moduleNameString (moduleName m)) `S.member` dsi_skippedModules dsi
    Nothing -> False

-- | Check if a Name is a skipped class
nameIsSkippedClass :: DerivSkipInfo -> Name -> Bool
nameIsSkippedClass dsi name =
  let occStr = T.pack (occNameString (nameOccName name))
      qualName = case nameModule_maybe name of
        Just m  -> T.pack (moduleNameString (moduleName m)) `T.append` T.pack "." `T.append` occStr
        Nothing -> occStr
  in qualName `S.member` dsi_skippedClasses dsi
     || occStr `S.member` dsi_skippedClasses dsi

-- | Collect all Names from an HsType
collectNamesFromHsType :: HsType GhcRn -> [Name]
collectNamesFromHsType = go
  where
    go (HsTyVar _ _ (L _ name))      = [name]
    go (HsAppTy _ (L _ t1) (L _ t2)) = go t1 ++ go t2
    go (HsFunTy _ _ (L _ t1) (L _ t2)) = go t1 ++ go t2
    go (HsListTy _ (L _ t))          = go t
    go (HsTupleTy _ _ ts)            = concatMap (go . unLoc) ts
    go (HsParTy _ (L _ t))           = go t
    go (HsQualTy _ (L _ ctxt) (L _ t)) = concatMap (go . unLoc) ctxt ++ go t
    go (HsForAllTy _ _ (L _ t))      = go t
    go (HsKindSig _ (L _ t) (L _ k)) = go t ++ go k
    go _                              = []

-- | Filter standalone deriving declarations, removing those that reference skipped modules/classes
filterStandaloneDerivs :: DerivSkipInfo -> [LDerivDecl GhcRn] -> [LDerivDecl GhcRn]
filterStandaloneDerivs dsi = filter (not . shouldSkipDerivDecl dsi . unLoc)

shouldSkipDerivDecl :: DerivSkipInfo -> DerivDecl GhcRn -> Bool
shouldSkipDerivDecl dsi dd =
  let wcType = deriv_type dd              -- LHsSigWcType GhcRn
      sig = unLoc (hswc_body wcType)      -- HsSig GhcRn
      body = unLoc (sig_body sig)         -- HsType GhcRn
      names = collectNamesFromHsType body
  in any (\n -> nameInSkippedModule dsi n || nameIsSkippedClass dsi n) names

-- | Filter deriving clauses from data declarations in TyClGroups
filterTyClGroupDerivs :: DerivSkipInfo -> [TyClGroup GhcRn] -> [TyClGroup GhcRn]
filterTyClGroupDerivs dsi = map filterGroup
  where
    filterGroup g = g { group_tyclds = map (fmap filterTyClDecl) (group_tyclds g) }

    filterTyClDecl (DataDecl ext name tvs fixity defn) =
      DataDecl ext name tvs fixity (filterDataDefnDerivs dsi defn)
    filterTyClDecl d = d

filterDataDefnDerivs :: DerivSkipInfo -> HsDataDefn GhcRn -> HsDataDefn GhcRn
filterDataDefnDerivs dsi defn = defn { dd_derivs = mapMaybe (filterDerivingClause dsi) (dd_derivs defn) }

filterDerivingClause :: DerivSkipInfo -> LHsDerivingClause GhcRn -> Maybe (LHsDerivingClause GhcRn)
filterDerivingClause dsi (L loc clause) =
  let (L dctLoc dct) = deriv_clause_tys clause
  in case dct of
    DctSingle ext ty ->
      let names = collectNamesFromHsType (unLoc (sig_body (unLoc ty)))
      in if any (\n -> nameInSkippedModule dsi n || nameIsSkippedClass dsi n) names
         then Nothing
         else Just (L loc clause)
    DctMulti ext tys ->
      let filtered = filter (not . hasSkippedName) tys
          hasSkippedName ty =
            let names = collectNamesFromHsType (unLoc (sig_body (unLoc ty)))
            in any (\n -> nameInSkippedModule dsi n || nameIsSkippedClass dsi n) names
      in if null filtered
         then Nothing
         else Just (L loc clause { deriv_clause_tys = L dctLoc (DctMulti ext filtered) })
#endif

addDerivedInstances :: GhcMonad m => DerivSkipInfo -> TypecheckedModule -> m TypecheckedModule
addDerivedInstances dsi tcm = do
#if __GLASGOW_HASKELL__ >= 910
    let Just (hsgroup, a, b, c, d) = tm_renamed_source tcm
    -- Filter out deriving declarations that reference skipped modules/classes
    let filteredDerivds = filterStandaloneDerivs dsi (hs_derivds hsgroup)
    let filteredTyclds  = filterTyClGroupDerivs dsi (hs_tyclds hsgroup)
    let hsgroup_filtered = hsgroup { hs_derivds = filteredDerivds, hs_tyclds = filteredTyclds }
#else
    let Just (hsgroup, a, b, c) = tm_renamed_source tcm
    let hsgroup_filtered = hsgroup
#endif

    -- Use error-tolerant deriving: if the all-at-once attempt fails,
    -- fall back to per-declaration processing so that individual
    -- failures (e.g. for Generic types, newtypes) don't block the
    -- successful derivations.
    mb_inst_infos <- initTcHackSafe tcm $ do
        let tcg_env = fst (tm_internals_ tcm)
            tcg_env_hack = tcg_env { tcg_mod = fakeDerivingMod, tcg_semantic_mod = fakeDerivingMod }
                -- Set the module to make it look like we are in GHCi
                -- so that GHC will allow us to re-typecheck existing instances
        setGblEnv tcg_env_hack $
#if __GLASGOW_HASKELL__ >= 910
            do (_, _, deriv_infos, _) <- tcTyAndClassDecls (hs_tyclds hsgroup_filtered)
               -- Try all standalone deriving declarations at once first
               (mb_result, _msgs) <- tryTc (tcInstDeclsDeriv deriv_infos (hs_derivds hsgroup_filtered))
               case mb_result of
                 Just (_gbl, infos, _binds) -> return infos
                 Nothing -> do
                   -- Fall back: process each standalone deriving declaration
                   -- individually, skipping any that fail
                   results <- forM (hs_derivds hsgroup_filtered) $ \deriv_decl -> do
                     (mb, _) <- tryTc (tcInstDeclsDeriv deriv_infos [deriv_decl])
                     return $ case mb of
                       Just (_, infos, _) -> infos
                       Nothing -> []
                   return (concat results)
#elif __GLASGOW_HASKELL__ >= 810
            do (_, _, deriv_info) <- tcTyAndClassDecls (hs_tyclds hsgroup_filtered)
               (mb_result, _msgs) <- tryTc (tcInstDeclsDeriv deriv_info (hs_derivds hsgroup_filtered))
               case mb_result of
                 Just (_gbl, infos, _binds) -> return infos
                 Nothing -> do
                   results <- forM (hs_derivds hsgroup_filtered) $ \deriv_decl -> do
                     (mb, _) <- tryTc (tcInstDeclsDeriv deriv_info [deriv_decl])
                     return $ case mb of
                       Just (_, infos, _) -> infos
                       Nothing -> []
                   return (concat results)
#else
            do (_gbl, infos, _binds) <- tcInstDeclsDeriv [] (hs_tyclds hsgroup_filtered >>= group_tyclds) (hs_derivds hsgroup_filtered)
               return infos
#endif

    let inst_infos = case mb_inst_infos of
          Just infos -> infos
          Nothing    -> []  -- If tcTyAndClassDecls itself failed, proceed without derived instances
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

#if __GLASGOW_HASKELL__ >= 910
    return $ tcm { tm_renamed_source = Just (hsgroup', a, b, c, d) }
#else
    return $ tcm { tm_renamed_source = Just (hsgroup', a, b, c) }
#endif

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

-- | Like 'initTcHack' but returns 'Nothing' on failure instead of throwing.
-- This allows the caller to proceed without derived instances when
-- tcTyAndClassDecls or other GHC internals fail.
initTcHackSafe :: GhcMonad m => TypecheckedModule -> TcM a -> m (Maybe a)
initTcHackSafe tcm action = do
 hsc_env <- getSession
 let hsc_env_tmp = hsc_env
        { hsc_dflags = ms_hspp_opts (pm_mod_summary (tm_parsed_module tcm)) }
 let mod = fakeDerivingMod
 let src_span = realSrcLocSpan (mkRealSrcLoc (fsLit "<deriving>") 1 1)

 result <- liftIO $ E.try @E.SomeException $
   initTc hsc_env_tmp HsSrcFile False mod src_span action
 case result of
   Right (_msgs, mba) -> return mba
   Left _exn          -> return Nothing

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
#if __GLASGOW_HASKELL__ >= 910
    , cid_ext = Nothing
#elif __GLASGOW_HASKELL__ >= 806
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
#if __GLASGOW_HASKELL__ >= 910
          NotPromoted Prefix (getName tc) (map (HsValArg noExtField . go) args')
#else
          NotPromoted Prefix (getName tc) (map (HsValArg . go) args')
#endif
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
