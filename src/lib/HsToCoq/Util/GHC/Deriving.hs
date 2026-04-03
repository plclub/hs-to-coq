{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

#if __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
#endif

#include "ghc-compat.h"

{- | Error-tolerant deriving pipeline for hs-to-coq.
Provides 'addDerivedInstances' which re-derives type class instances after
typechecking, with skip-aware filtering ('DerivSkipInfo') and per-declaration
retry on failure. Bridges the GHC deriving API with hs-to-coq's conversion. -}

module HsToCoq.Util.GHC.Deriving (initForDeriving, addDerivedInstances, DerivSkipInfo(..)) where

import GHC

import Control.Monad
import Data.Maybe (isNothing, mapMaybe)
import qualified Data.Set as S
import qualified Data.Text as T

-- GHC version-gated imports: GHC 9.0+ reorganized internal modules under
-- GHC.* hierarchies; older versions use flat module names (e.g. TcRnMonad).
#if __GLASGOW_HASKELL__ >= 900
import GHC.Plugins
import GHC.Parser.Annotation (noAnn)
#elif __GLASGOW_HASKELL__ >= 808
import GhcPlugins (SourceText(NoSourceText), PromotionFlag(NotPromoted))
#else
import GhcPlugins (SourceText(NoSourceText))
#endif

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

-- | Carries skip/axiomatize info from the edits system into the deriving
-- pipeline, so 'addDerivedInstances' can filter out deriving declarations
-- for types whose modules are skipped or whose classes are not available.
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

-- | Check if a Name belongs to a skipped module or is a skipped class.
shouldSkipName :: DerivSkipInfo -> Name -> Bool
shouldSkipName dsi n = nameInSkippedModule dsi n || nameIsSkippedClass dsi n

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

-- | Filter standalone deriving declarations based on 'DerivSkipInfo'.
-- Removes declarations that would fail during typechecking because they
-- reference types from skipped/axiomatized modules or skipped classes
-- (e.g. @deriving instance Generic Foo@ when Generic is skipped).
filterStandaloneDerivs :: DerivSkipInfo -> [LDerivDecl GhcRn] -> [LDerivDecl GhcRn]
filterStandaloneDerivs dsi = filter (not . shouldSkipDerivDecl dsi . unLoc)

shouldSkipDerivDecl :: DerivSkipInfo -> DerivDecl GhcRn -> Bool
shouldSkipDerivDecl dsi dd =
  let wcType = deriv_type dd              -- LHsSigWcType GhcRn
      sig = unLoc (hswc_body wcType)      -- HsSig GhcRn
      body = unLoc (sig_body sig)         -- HsType GhcRn
      names = collectNamesFromHsType body
  in any (shouldSkipName dsi) names

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
    DctSingle _ext ty ->
      let names = collectNamesFromHsType (unLoc (sig_body (unLoc ty)))
      in if any (shouldSkipName dsi) names
         then Nothing
         else Just (L loc clause)
    DctMulti ext tys ->
      let filtered = filter (not . hasSkippedName) tys
          hasSkippedName ty =
            let names = collectNamesFromHsType (unLoc (sig_body (unLoc ty)))
            in any (shouldSkipName dsi) names
      in if null filtered
         then Nothing
         else Just (L loc clause { deriv_clause_tys = L dctLoc (DctMulti ext filtered) })
#endif

-- | Re-derive instances after typechecking, using an error-tolerant strategy.
-- Unlike GHC's all-or-nothing approach, this tries all derivations at once
-- first, then falls back to processing each one individually on failure.
-- Individual failures (e.g. Generic, newtypes with unsupported coercions) are
-- silently dropped so that successful derivations still proceed.
addDerivedInstances :: GhcMonad m => DerivSkipInfo -> TypecheckedModule -> m TypecheckedModule
addDerivedInstances dsi tcm = do
#if __GLASGOW_HASKELL__ >= 910
    (hsgroup, a, b, c, d) <- case tm_renamed_source tcm of
      Just x  -> pure x
      Nothing -> error "addDerivedInstances: TypecheckedModule has no renamed source"
    -- Filter out deriving declarations that reference skipped modules/classes
    let filteredDerivds = filterStandaloneDerivs dsi (hs_derivds hsgroup)
    let filteredTyclds  = filterTyClGroupDerivs dsi (hs_tyclds hsgroup)
    let hsgroup_filtered = hsgroup { hs_derivds = filteredDerivds, hs_tyclds = filteredTyclds }
#else
    (hsgroup, a, b, c) <- case tm_renamed_source tcm of
      Just x  -> pure x
      Nothing -> error "addDerivedInstances: TypecheckedModule has no renamed source"
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
               -- Try all derivations at once first
               (mb_result, _msgs) <- tryTc (tcInstDeclsDeriv deriv_infos (hs_derivds hsgroup_filtered))
               case mb_result of
                 Just (_gbl, infos, _binds) -> return infos
                 Nothing -> do
                   -- Batch derivation failed; fall back to per-declaration retry
                   liftIO $ putStrLn "hs-to-coq: deriving: batch derivation failed, trying individually"
                   derivResults <- forM deriv_infos $ \di -> do
                     (mb, _) <- tryTc (tcInstDeclsDeriv [di] [])
                     return $ case mb of
                       Just (_, infos, _) -> infos
                       Nothing -> []
                   standaloneResults <- forM (hs_derivds hsgroup_filtered) $ \deriv_decl -> do
                     (mb, _) <- tryTc (tcInstDeclsDeriv [] [deriv_decl])
                     return $ case mb of
                       Just (_, infos, _) -> infos
                       Nothing -> []
                   return (concat derivResults ++ concat standaloneResults)
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

    inst_infos <- case mb_inst_infos of
          Just infos -> pure infos
          Nothing    -> do  -- If tcTyAndClassDecls itself failed, proceed without derived instances
            liftIO $ putStrLn "hs-to-coq: WARNING: entire deriving pipeline failed, proceeding with 0 derived instances"
            pure []
    let inst_decls = map instInfoToDecl inst_infos

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

_initTcHack :: GhcMonad m => TypecheckedModule -> TcM a -> m a
_initTcHack tcm action = do
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

-- | Like 'initTcHack' but returns 'Maybe' instead of crashing on failure.
-- 'initTcHack' throws a 'SourceError' when the TcM action fails;
-- this variant catches all exceptions and returns 'Nothing', allowing
-- graceful fallback when typechecking fails (e.g. missing TyCon info).
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
   Right (_msgs, mba) -> do
     when (isNothing mba) $
       liftIO $ putStrLn "hs-to-coq: deriving: initTc returned Nothing (type errors in derived code)"
     return mba
   Left exn
     | Just (_ :: E.AsyncException) <- E.fromException exn -> liftIO $ E.throwIO exn
     | otherwise -> do
         liftIO $ putStrLn $ "hs-to-coq: deriving: initTc threw exception: " ++ show exn
         return Nothing

fakeDerivingMod :: Module
fakeDerivingMod = mkModule
#if __GLASGOW_HASKELL__ >= 900
  interactiveUnit
#else
  interactiveUnitId
#endif
  (mkModuleName "Deriving")


-- | Convert a derived 'InstInfo' back into a source-level 'LInstDecl'.
-- GHC 9.0+ changed type signature representation: 'HsIB' was replaced by
-- 'HsSig' with 'HsOuterImplicit' for implicit type variable binding.
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

-- Taken from HsUtils. We need it to produce a Name, not a RdrName.
-- GHC 9.0+ changes: 'splitFunTy' returns a 3-tuple (multiplicity, arg, res)
-- for linear types support; 'ForAllTy' uses 'HsForAllInvis'/'hst_tele'
-- instead of 'hst_bndrs'/'hst_fvf'; 'go_tv' gains a 'Specificity' parameter.
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
    go (LitTy (NumTyLit n))  = noLoc $ HsTyLit NOEXT (HsNumTy NoSourceText n)
    go (LitTy (StrTyLit s))  = noLoc $ HsTyLit NOEXT (HsStrTy NoSourceText s)
    go (LitTy (CharTyLit c)) = noLoc $ HsTyLit NOEXT (HsCharTy NoSourceText c)
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
