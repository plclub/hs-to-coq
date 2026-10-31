{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 910
{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TypeFamilies #-}

-- GHC recognizes stock classes by their unit-qualified Names. A source copy
-- of ghc-internal in the translator's dummy unit has different Names. Reuse
-- GHC's generator only after checking the source class against its stock API;
-- leave the source class and the final typecheck's dictionaries unchanged.
module HsToRocq.Util.GHC.StockDeriving
  ( StockExpansion, stockExpansionSpan
  , expandStockDeriving, verifyStockExpansions
  ) where

import Control.Monad
import Control.Monad.Trans.Reader (runReaderT)
import qualified Control.Exception as E
import Data.Generics (everywhere, mkT)
import Data.List (sortOn)
import Data.Maybe (isJust, isNothing)

import GHC
import GHC.Plugins
import GHC.Parser.Annotation
import GHC.Data.Bag (isEmptyBag)
import GHC.Core.Class
import GHC.Core.InstEnv (instEnvElts, is_dfun)
import GHC.Types.Name.Reader (lookupGRE_Name)
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.Env (tcLookupClass)
import GHC.Tc.Utils.TcType (tcSplitDFunTy, tcSplitMethodTy, eqType, eqTypes)
import GHC.Tc.Gen.HsType (tcHsClsInstType)
import GHC.Tc.TyCl (tcTyAndClassDecls)
import GHC.Tc.Deriv.Functor (gen_Traversable_binds, gen_Foldable_binds)
import GHC.Tc.Deriv.Generate (DerivInstTys(..), buildDataConInstArgEnv)
import GHC.Tc.Deriv.Utils
import GHC.Tc.Types.Origin (SkolemInfoAnon(DerivSkol), UserTypeCtxt(InstDeclCtxt), mkSkolemInfo)
import GHC.Tc.Errors.Types (TcRnMessage(TcRnCannotDeriveInstance), DeriveInstanceErrReason(DerivErrDataConsNotAllInScope), mkTcRnUnknownMessage, usingGeneralizedNewtypeDeriving)
import GHC.Builtin.Names (traversableClassName, foldableClassName)
import GHC.Types.Error (mkPlainDiagnostic, DiagnosticReason(ErrorWithoutFlag))
import GHC.Types.SourceError (mkSrcErr)
import GHC.Types.SourceFile (HscSource(HsSrcFile))
import GHC.Driver.Errors.Types (GhcMessage(GhcTcRnMessage))
import GHC.Unit.Module.ModDetails (md_insts)
import qualified GHC.LanguageExtensions as LangExt

-- Retain the original request span and source-class type, not a dictionary
-- generated in the installed class's environment. The final GHC check must
-- provide exactly one dictionary with this type.
data StockExpansion = StockExpansion
  { stockExpansionSpan :: SrcSpan
  , stockExpansionType :: Type
  }

expandStockDeriving :: GhcMonad m
  => ParsedModule -> TcGblEnv -> HsGroup GhcRn -> LDerivDecl GhcRn
  -> m (Maybe (ParsedModule, StockExpansion))
expandStockDeriving pm renamedEnv group request
  | moduleNameString (moduleName (tcg_mod renamedEnv)) `notElem`
      ["GHC.Internal.Data.Traversable", "GHC.Internal.Data.Foldable"] = pure Nothing
  | not (stockStrategy (deriv_strategy (unLoc request))) = pure Nothing
  | otherwise = inRenamedEnvironment pm renamedEnv (getLocA request) $ do
      (gbl, _, _, _) <- tcTyAndClassDecls (hs_tyclds group)
      setGblEnv gbl $ do
        let decl = unLoc request
        dfunTy <- tcHsClsInstType (InstDeclCtxt True) (hswc_body (deriv_type decl))
        let (tvs, theta, cls, args) = tcSplitDFunTy dfunTy
            sourceName = getName cls
        home <- getModule
        case (nameModule_maybe sourceName == Just home,
              moduleNameString (moduleName home), occNameString (nameOccName sourceName)) of
          (True, "GHC.Internal.Data.Traversable", "Traversable") ->
            generate home dfunTy tvs theta cls args traversableClassName gen_Traversable_binds
          (True, "GHC.Internal.Data.Foldable", "Foldable") ->
            generate home dfunTy tvs theta cls args foldableClassName gen_Foldable_binds
          _ -> pure Nothing
  where
    stockStrategy Nothing = True
    stockStrategy (Just (L _ (StockStrategy _))) = True
    stockStrategy _ = False

    generate home dfunTy tvs theta cls args canonicalName generator = do
      canonical <- tcLookupClass canonicalName
      unless (compatibleClass cls canonical) $
        reject "source class is incompatible with GHC's stock deriving API"
      (tc, tcArgs) <- case args of
        [arg] | Just (tc, tcArgs) <- splitTyConApp_maybe arg
              , isAlgTyCon tc, not (isDataFamilyTyCon tc)
              , tyConArity tc == length tcArgs + 1 -> pure (tc, tcArgs)
        _ -> reject "stock generator bridge requires an ordinary unary datatype constructor application"
      let dit = DerivInstTys [] tc tcArgs tc tcArgs (buildDataConInstArgEnv tc tcArgs)
      skol <- mkSkolemInfo (DerivSkol dfunTy)
      let denv = DerivEnv (unLoc <$> deriv_overlap_mode (unLoc request)) tvs canonical args
                         (SupplyContext theta) skol Nothing Nothing
          rejectStock reason = do
            gnd <- xoptM LangExt.GeneralizedNewtypeDeriving
            failWithTc (TcRnCannotDeriveInstance cls args Nothing (usingGeneralizedNewtypeDeriving gnd) reason)
      status <- runReaderT (checkOriginativeSideConditions dit) denv
      case status of
        CanDeriveStock _ -> pure ()
        StockClassError reason -> rejectStock reason
        _ -> reject "GHC's stock side conditions reject this derivation"
      -- GHC.Tc.Deriv.doDerivInstErrorChecks1 performs this additional stock
      -- check outside checkOriginativeSideConditions. Exact imported names
      -- in the generator's output must not bypass constructor visibility.
      rdrEnv <- getGlobalRdrEnv
      when (not (isWiredIn tc) &&
            (isAbstractTyCon tc || any (isNothing . lookupGRE_Name rdrEnv . dataConName) (tyConDataCons tc))) $
        rejectStock (DerivErrDataConsNotAllInScope tc)
      let (binds, aux) = generator (getLocA (hswc_body (deriv_type (unLoc request)))) dit
      unless (isEmptyBag aux) $ reject "unexpected auxiliary bindings from stock generator"
      let methods = map (nameOccName . getName) (classMethods cls)
          rebind :: RdrName -> RdrName
          rebind rdr
            | Orig m occ <- rdr, m == nameModule canonicalName, occ `elem` methods = Unqual occ
            | Exact n <- rdr, nameModule_maybe n == Just home = Unqual (nameOccName n)
            | otherwise = rdr
          -- Selectors and local constructors must be resolved in the source
          -- class's module again; imported constructor Names remain exact.
          sourceBinds = everywhere (mkT rebind) binds
          rewrite (L loc (DerivD _ parsedDecl)) | locA loc == getLocA request =
            L loc $ InstD noExtField $ ClsInstD noExtField $ ClsInstDecl
              { cid_ext = (Nothing, [], NoAnnSortKey)
              , cid_poly_ty = hswc_body (deriv_type parsedDecl)
              , cid_binds = sourceBinds
              , cid_sigs = []
              , cid_tyfam_insts = []
              , cid_datafam_insts = []
              , cid_overlap_mode = deriv_overlap_mode parsedDecl }
          rewrite other = other
          L loc source = pm_parsed_source pm
          expanded = pm { pm_parsed_source = L loc source { hsmodDecls = map rewrite (hsmodDecls source) } }
      pure $ Just (expanded, StockExpansion (getLocA request) dfunTy)

-- Check types with GHC equality after alpha-renaming class/method variables.
-- Occurrence names select corresponding methods only after the exact source
-- module and class identity guard. They never replace class identity.
compatibleClass :: Class -> Class -> Bool
compatibleClass source canonical =
  eqType (tyConKind (classTyCon source)) (tyConKind (classTyCon canonical)) &&
  null (classATs source) && null (classATs canonical) &&
  null (snd (classTvsFds source)) && null (snd (classTvsFds canonical)) &&
  defaults source == defaults canonical &&
  eqTypes (map adapt (classSCTheta source)) (classSCTheta canonical) &&
  map (nameOccName . getName) sourceMethods == map (nameOccName . getName) canonicalMethods &&
  and (zipWith sameMethod sourceMethods canonicalMethods)
  where
    adapt = substTyWith (classTyVars source) (mkTyVarTys (classTyVars canonical))
    defaults = sortOn fst . map (\(method, def) -> (nameOccName (getName method), isJust def)) . classOpItems
    ordered = sortOn (nameOccName . getName) . classMethods
    sourceMethods = ordered source
    canonicalMethods = ordered canonical
    sameMethod l c =
      let (ltvs, _, lt) = tcSplitMethodTy (varType l)
          (ctvs, _, ct) = tcSplitMethodTy (varType c)
      in length ltvs == length ctvs && eqType (substTyWith ltvs (mkTyVarTys ctvs) lt) ct

reject :: String -> TcM a
reject = failWithTc . mkTcRnUnknownMessage . mkPlainDiagnostic ErrorWithoutFlag [] . text

inRenamedEnvironment :: GhcMonad m => ParsedModule -> TcGblEnv -> SrcSpan -> TcM a -> m a
inRenamedEnvironment pm renamedEnv span action = do
  env <- getSession
  let flags = ms_hspp_opts (pm_mod_summary pm)
      loc = case span of
        RealSrcSpan real _ -> real
        _ -> realSrcLocSpan (mkRealSrcLoc (fsLit "<stock-deriving>") 1 1)
  (messages, result) <- liftIO $ initTc env { hsc_dflags = flags }
    HsSrcFile False (tcg_mod renamedEnv) loc (setGblEnv renamedEnv (setSrcSpan span action <* failIfErrsM))
  maybe (liftIO $ E.throwIO $ mkSrcErr $ fmap GhcTcRnMessage messages) pure result

verifyStockExpansions :: GhcMonad m => [StockExpansion] -> TypecheckedModule -> m ()
verifyStockExpansions expanded tcm = do
  let instances = instEnvElts (md_insts (snd (tm_internals_ tcm)))
  forM_ expanded $ \expansion ->
    unless (length (filter (eqType (stockExpansionType expansion) . varType . is_dfun) instances) == 1) $
      liftIO $ E.throwIO $ userError $
        showSDocUnsafe (ppr (stockExpansionSpan expansion)) ++
        ": stock-generated instance must have exactly one checked dictionary: " ++
        showSDocUnsafe (ppr (stockExpansionType expansion))
#else
module HsToRocq.Util.GHC.StockDeriving () where
#endif
