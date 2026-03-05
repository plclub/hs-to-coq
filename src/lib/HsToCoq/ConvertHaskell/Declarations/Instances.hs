{-# LANGUAGE CPP,
             TupleSections,
             LambdaCase,
             RecordWildCards,
             OverloadedStrings,
             ScopedTypeVariables,
             FlexibleContexts #-}
#include "ghc-compat.h"

module HsToCoq.ConvertHaskell.Declarations.Instances (
  convertClsInstDecls
) where

import Control.Lens

import Data.Semigroup (Semigroup(..), (<>))
import Data.Traversable
import HsToCoq.Util.Traversable
import Data.Maybe
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Bifunctor
import Data.List (partition, sortBy)
import Data.Monoid
import Data.Ord (comparing)
import qualified Data.Text as T
import Control.Monad.Reader.Class

import Control.Monad.State

import qualified Data.Map.Strict as M

import GHC hiding (Name)
#if __GLASGOW_HASKELL__ >= 900
import GHC.Data.Bag (bagToList)
#else
import Bag
#endif
#if __GLASGOW_HASKELL__ >= 806
import HsToCoq.Util.GHC.HsTypes (noExtCon)
#endif
import HsToCoq.Util.GHC.Module
import HsToCoq.Util.Monad (ErrorString)

import HsToCoq.Coq.Gallina

import HsToCoq.Coq.Subst
import HsToCoq.Coq.SubstTy
import HsToCoq.Coq.Pretty
import HsToCoq.Coq.Gallina.Util

import HsToCoq.Edits.Types
import HsToCoq.ConvertHaskell.Monad
import HsToCoq.ConvertHaskell.Variables
import HsToCoq.ConvertHaskell.TypeInfo
import HsToCoq.ConvertHaskell.Definitions
import HsToCoq.ConvertHaskell.HsType
import HsToCoq.ConvertHaskell.Expr
import HsToCoq.ConvertHaskell.Axiomatize
import HsToCoq.ConvertHaskell.Declarations.Class
import HsToCoq.ConvertHaskell.TypeEnv.TyCl
import HsToCoq.ConvertHaskell.TypeEnv.Instances

import qualified Data.Set as S

--------------------------------------------------------------------------------

-- | Check if a type name is a single-constructor, single-field type (newtype).
-- Returns (constructor, accessor) if so.
lookupNewtypeInfo :: ConversionMonad r m
                  => Qualid -> m (Maybe (Qualid, Qualid))
lookupNewtypeInfo typeName = do
    mcons <- lookupConstructors typeName
    case mcons of
      Just [con] -> do
        mfields <- lookupConstructorFields con
        case mfields of
          Just (RecordFields [field]) -> pure $ Just (con, field)
          Just (NonRecordFields 1)    -> pure $ Just (con, con) -- no accessor
          _                           -> pure Nothing
      _ -> pure Nothing

-- | Extract the head type constructor from a Gallina type term.
-- e.g. (Min inst_a) -> Just "Min", (list a) -> Just "list"
typeHead :: Term -> Maybe Qualid
typeHead (Qualid q)                      = Just q
typeHead (App (Qualid q) _)              = Just q
typeHead (Parens t)                      = typeHead t
typeHead (InScope t _)                   = typeHead t
typeHead _                               = Nothing

-- | Decompose an arrow type into arguments and result, skipping forall binders.
-- Returns ([argTypes], resultType)
decomposeArrowType :: Term -> ([Term], Term)
decomposeArrowType (Forall _ t)  = decomposeArrowType t
decomposeArrowType (Arrow a b)   = let (args, ret) = decomposeArrowType b
                                   in (a : args, ret)
decomposeArrowType (Parens t)    = decomposeArrowType t
decomposeArrowType t             = ([], t)

-- | Count the forall binders in a type (to generate matching implicit args).
countForallBinders :: Term -> Int
countForallBinders (Forall bs t) = length (NE.toList bs) + countForallBinders t
countForallBinders _             = 0

-- | Expand a coerce-based definition body using explicit newtype wrapping.
-- If the body contains GHC.Prim.coerce and we can determine the newtype
-- constructors from the declared type, replace coerce with explicit
-- pattern matching (unwrap arguments, apply function, wrap result).
expandCoerce :: ConversionMonad r m
             => [Binder]    -- ^ The definition's explicit arguments
             -> Maybe Term  -- ^ The declared type (if available)
             -> Term        -- ^ The definition body
             -> m Term
expandCoerce defArgs mDeclType body = case stripFunBinders body of
    -- Strip any leading fun binders (implicit or explicit) from body
    -- and work on the inner coerce expression
    (outerBinders, innerBody) -> case innerBody of

      -- Pattern: GHC.Prim.coerce (f : srcType) with parens
      App (Qualid (Qualified "GHC.Prim" "coerce"))
          (PosArg (Parens (HasType innerFn _srcType)) :| [])
        | Just declType <- mDeclType
        -> rewrap outerBinders <$> expandCoerceWithTypes defArgs declType innerFn

      -- Pattern: GHC.Prim.coerce (f : srcType) without parens
      App (Qualid (Qualified "GHC.Prim" "coerce"))
          (PosArg (HasType innerFn _srcType) :| [])
        | Just declType <- mDeclType
        -> rewrap outerBinders <$> expandCoerceWithTypes defArgs declType innerFn

      -- Pattern: GHC.Prim.coerce (f) with parens (no type annotation)
      App (Qualid (Qualified "GHC.Prim" "coerce"))
          (PosArg (Parens innerFn) :| [])
        | Just declType <- mDeclType
        -> rewrap outerBinders <$> expandCoerceWithTypes defArgs declType innerFn

      -- Pattern: GHC.Prim.coerce f without parens (no type annotation)
      App (Qualid (Qualified "GHC.Prim" "coerce"))
          (PosArg innerFn :| [])
        | Just declType <- mDeclType
        -> rewrap outerBinders <$> expandCoerceWithTypes defArgs declType innerFn

      -- Pattern: bare GHC.Prim.coerce used as a function
      Qualid (Qualified "GHC.Prim" "coerce")
        | Just declType <- mDeclType
        -> rewrap outerBinders <$> expandBareCoerce defArgs declType

      -- Pattern: GHC.Prim.coerce (f : srcType) :: dstType (old GHC 8.x pattern)
      HasType app@(App (Qualid (Qualified "GHC.Prim" "coerce"))
                       (PosArg (Parens (Qualid _)) :| [])) _
        -> pure $ rewrap outerBinders app  -- existing hack: just strip type ascription

      _ -> pure body
  where
    -- Strip leading Fun binders to expose the inner coerce body
    stripFunBinders :: Term -> ([NonEmpty Binder], Term)
    stripFunBinders (Fun bs inner) =
      let (rest, core) = stripFunBinders inner
      in (bs : rest, core)
    stripFunBinders t = ([], t)

    -- Re-wrap an expanded body with the stripped binders
    rewrap :: [NonEmpty Binder] -> Term -> Term
    rewrap [] t     = t
    rewrap (bs:rest) t = Fun bs (rewrap rest t)

-- | Expand coerce when we have a typed inner function and a declared type.
expandCoerceWithTypes :: ConversionMonad r m
                      => [Binder] -> Term -> Term -> m Term
expandCoerceWithTypes defArgs declType innerFn = do
    let (argTypes, retType) = decomposeArrowType declType
        nImplicit = countForallBinders declType
    -- Try to find newtype info for argument and return types
    argInfos <- mapM getNewtypeWrap argTypes
    retInfo  <- getNewtypeWrap retType
    -- If at least one argument or the return type is a newtype, expand
    if any isNewtype argInfos || isNewtype retInfo
      then buildExpandedBody nImplicit defArgs argInfos retInfo innerFn
      else pure $ App (Qualid (Qualified "GHC.Prim" "coerce"))
                      (PosArg (Parens innerFn) :| [])

-- | Expand bare coerce (used as identity-like function between newtype and base type).
-- For bare coerce, we generate an explicit lambda that unwraps newtype args,
-- applies any function args, and wraps the result.
expandBareCoerce :: ConversionMonad r m
                 => [Binder] -> Term -> m Term
expandBareCoerce _defArgs declType = do
    let (argTypes, retType) = decomposeArrowType declType
    argInfos <- mapM getNewtypeWrap argTypes
    retInfo  <- getNewtypeWrap retType
    if any isNewtype argInfos || isNewtype retInfo
      then do
        let varNames = [ Bare (T.pack ("arg_" ++ show i ++ "__"))
                       | i <- [0 :: Int .. length argTypes - 1] ]
            indexed = zip3 [0::Int ..] argInfos varNames
            innerExpr = buildInnerExpr indexed retInfo
            explicitArgs = [ExplicitBinder (Ident v) | v <- varNames]
        case NE.nonEmpty explicitArgs of
          Just binders -> pure $ Fun binders innerExpr
          Nothing      -> pure $ Qualid (Qualified "GHC.Prim" "coerce")
      else pure $ Qualid (Qualified "GHC.Prim" "coerce")
  where
    -- Build the inner expression for bare coerce
    -- For single arg: wrap(unwrap(arg))
    -- For multi arg like (a->b->c) -> F a -> F b -> F c:
    --   apply first non-newtype arg to remaining unwrapped args, then wrap
    buildInnerExpr :: [(Int, NewtypeWrap, Qualid)] -> NewtypeWrap -> Term
    buildInnerExpr indexed retInfo =
      let (fnArgs, dataArgs) = partition (\(_, nw, _) -> not (isNewtype nw)) indexed
          unwrapped = [(i, unwrapArg nw (Qualid v)) | (i, nw, v) <- dataArgs]
          fnTerms = [(i, Qualid v) | (i, _, v) <- fnArgs]
          allTerms = map snd $ sortBy (comparing fst) (unwrapped ++ fnTerms)
          applied = case allTerms of
            []     -> Qualid (Qualified "GHC.Prim" "coerce")
            [x]    -> x
            (f:xs) -> foldl (\acc a -> App acc (PosArg a :| [])) f xs
      in wrapResult retInfo applied

data NewtypeWrap = IsNewtype Qualid Qualid  -- constructor, accessor
                 | NotNewtype
                 deriving (Eq)

isNewtype :: NewtypeWrap -> Bool
isNewtype (IsNewtype _ _) = True
isNewtype _               = False

getNewtypeWrap :: ConversionMonad r m => Term -> m NewtypeWrap
getNewtypeWrap ty = case typeHead ty of
    Just q  -> do
      minfo <- lookupNewtypeInfo q
      case minfo of
        Just (con, acc) -> pure $ IsNewtype con acc
        Nothing         -> pure NotNewtype
    Nothing -> pure NotNewtype

unwrapArg :: NewtypeWrap -> Term -> Term
unwrapArg (IsNewtype _con acc) var = App (Qualid acc) (PosArg var :| [])
unwrapArg NotNewtype            var = var

wrapResult :: NewtypeWrap -> Term -> Term
wrapResult (IsNewtype con _acc) inner = App (Qualid con) (PosArg inner :| [])
wrapResult NotNewtype            inner = inner

-- | Build the expanded function body with explicit wrapping/unwrapping.
buildExpandedBody :: ConversionMonad r m
                  => Int -> [Binder] -> [NewtypeWrap] -> NewtypeWrap -> Term -> m Term
buildExpandedBody _nImplicit _defArgs argInfos retInfo innerFn = do
    let varNames = [ Bare (T.pack ("arg_" ++ show i ++ "__"))
                   | i <- [0 :: Int .. length argInfos - 1] ]
        unwrappedArgs = zipWith unwrapArg argInfos (map Qualid varNames)
        innerApp = foldl (\f a -> App f (PosArg a :| [])) innerFn unwrappedArgs
        wrappedResult = wrapResult retInfo innerApp
        binders = [ExplicitBinder (Ident v) | v <- varNames]
    case NE.nonEmpty binders of
      Just bs -> pure $ Fun bs wrappedResult
      Nothing -> pure wrappedResult

--------------------------------------------------------------------------------

-- Take the instance head and make it into a valid identifier.
convertInstanceNameAndTy :: ConversionMonad r m => LHsType GhcRn -> m (Qualid, Qualid)
convertInstanceNameAndTy n = do
    coqType <- withCurrentDefinition (Bare "") $ convertLHsType n -- revisit if needed
    qual <- views (currentModule.modName) $ Qualified . moduleNameText
    case skip coqType of
        Left err -> throwProgramError $ "Cannot derive instance name from `" ++ showP coqType ++ "': " ++ err
        Right (name, ty) -> return (qual name, ty)
  where
    -- Skip type variables and constraints
    skip (Forall _ t)  = skip t
    skip (Arrow _ t)   = skip t
    skip (InScope t _) = skip t
    skip t             = do
      t' <- bfTerm t
      -- The [head $ tail] below will not be correct with multi-param type classes
      pure (bfToName t', head $ tail t')

    bfToName :: [Qualid] -> T.Text
    bfToName qids | isVanilla = name
                  | otherwise = name <> "__" <> T.pack (show shapeNum)
      where
        tyCons = catMaybes (unTyCon <$> qids)
        name = T.intercalate "__" tyCons
        shapeNum = bitsToInt $ map isTyCon qids

        -- A vanilla header is when all tyCons appear before all
        -- type variables. In this case, do not add the shapeNum
        isVanilla = not $ any isTyCon $ dropWhile isTyCon qids

        isTyCon = isJust . unTyCon

        unTyCon :: Qualid -> Maybe T.Text
        unTyCon (Qualified _ base)  = Just base
        unTyCon (Bare "bool")       = Just "bool"
        unTyCon (Bare "comparison") = Just "comparison"
        unTyCon (Bare "list")       = Just "list"
        unTyCon (Bare "option")     = Just "option"
        unTyCon (Bare "op_zt__")    = Just "op_zt__"
        unTyCon (Bare "unit")       = Just "unit"
        unTyCon (Bare "nat")        = Just "nat"
        unTyCon _                   = Nothing

        bitsToInt :: [Bool] -> Integer
        bitsToInt []         = 0
        bitsToInt (True:xs)  = 2*bitsToInt xs + 1
        bitsToInt (False:xs) = 2*bitsToInt xs

    -- Breadth-first traversal listing all variables and type constructors
    bfTerm :: Term -> Either ErrorString [Qualid]
    bfTerm = fmap concat . go
      where
        go :: Term -> Either ErrorString [[Qualid]]
        go t = do
            (f, args) <- collectArgs t
            subtrees <- mapM go args
            return $ [f] : foldr merge [] subtrees

    merge :: [[a]] -> [[a]] -> [[a]]
    merge xs     []     = xs
    merge []     ys     = ys
    merge (x:xs) (y:ys) = (x ++ y) : merge xs ys

--------------------------------------------------------------------------------
{- Haskell:
      instance Functor ((->) r)
   InstanceInfo
      Name = "Functor__arr_r___"
      Head = "Functor (_(->)_ r)" as a Coq term, with free variable
      Class = "Functor"

   Haskell:
      instance Eq a => Eq [a]
   InstanceInfo
      Name = "Eq_list____"
      Head = "forall `{Eq a}, Eq (list a)"
      Class = "Eq"

-}
data InstanceInfo = InstanceInfo { instanceName       :: !Qualid
                                 , instanceHead       :: !Term
                                 , instanceClass      :: !Qualid
                                 , instanceTy         :: !Qualid
                                 }
                  deriving (Eq, Ord, Show, Read)

-- TODO use LocalConvMonad instead?
convertClsInstDeclInfo :: ConversionMonad r m => ClsInstDecl GhcRn -> m InstanceInfo
convertClsInstDeclInfo ClsInstDecl{..} = do
#if __GLASGOW_HASKELL__ >= 900
  let unwrapSigType = sig_body . unLoc
#else
  let unwrapSigType = hsib_body
#endif
  (instanceName, instanceTy)  <- convertInstanceNameAndTy $ unwrapSigType cid_poly_ty
  utvm                        <- unusedTyVarModeFor instanceName
  instanceHead                <- withCurrentDefinition instanceName $ convertLHsSigType utvm cid_poly_ty
  instanceClass               <- termHead instanceHead
                                 & maybe (convUnsupportedIn "strangely-formed instance heads"
                                           "type class instance"
                                           (showP instanceName))
                                 pure

  pure InstanceInfo{..}
#if __GLASGOW_HASKELL__ >= 806
convertClsInstDeclInfo (XClsInstDecl v) = noExtCon v
#endif

--------------------------------------------------------------------------------

no_class_error :: MonadIO m => Qualid -> String -> m a
no_class_error cls extra = throwProgramError $  "Could not find information for the class " ++ quote_qualid cls
                                             ++ if null extra then [] else ' ':extra

no_class_instance_error :: MonadIO m => Qualid -> Qualid -> m a
no_class_instance_error cls inst = no_class_error cls $ "when defining the instance " ++ quote_qualid inst

no_class_method_error :: MonadIO m => Qualid -> Qualid -> m a
no_class_method_error cls meth = no_class_error cls $ "when defining the method " ++ quote_qualid meth


quote_qualid :: Qualid -> String
quote_qualid qid = "`" ++ showP qid ++ "'"

--------------------------------------------------------------------------------

unlessSkippedClass :: ConversionMonad r m => InstanceInfo -> m [Sentence] -> m [Sentence]
unlessSkippedClass InstanceInfo{..} act = do
  view (edits.skippedClasses.contains instanceClass) >>= \case
    True ->
      pure [CommentSentence . Comment $
              "Skipping all instances of class `" <> textP instanceClass
                <> "', including `" <> textP instanceName <> "'"]
    False ->
      act

bindsToMap :: ConversionMonad r m => [HsBindLR GhcRn GhcRn] -> m (M.Map Qualid (HsBind GhcRn))
bindsToMap binds = fmap M.fromList $ forM binds $ \hs_bind -> do
    name <- hsBindName hs_bind
    return (name, hs_bind)

clsInstFamiliesToMap :: ConversionMonad r m => [LTyFamInstDecl GhcRn] -> m (M.Map Qualid (HsType GhcRn))
clsInstFamiliesToMap assocTys =
  fmap M.fromList . for assocTys $
#if __GLASGOW_HASKELL__ >= 900
    \(L _ (TyFamInstDecl _ FamEqn{..})) ->
#else
    \(L _ (TyFamInstDecl HsIB {hsib_body = FamEqn{..}})) ->
#endif
    (, unLoc feqn_rhs) <$> var TypeNS (unLoc feqn_tycon)

-- Module-local
data Conv_Method = CM_Renamed            Sentence
                 | CM_Defined Conv_Level Term
                 deriving (Eq, Ord, Show, Read)

-- Module-local
data Conv_Level = CL_Term | CL_Type deriving (Eq, Ord, Enum, Bounded, Show, Read)

convertClsInstDecl :: forall r m. ConversionMonad r m => ConvertedInstanceEnv -> ClsInstDecl GhcRn -> m [Sentence]
convertClsInstDecl env cid@ClsInstDecl{..} = do
  ii@InstanceInfo{..} <- convertClsInstDeclInfo cid
  let convUnsupportedHere what = convUnsupportedIn what "type class instance" (showP instanceName)

  let err_handler exn = pure [ translationFailedComment ("instance " <> qualidBase instanceName) exn ]
  unlessSkippedClass ii . handleIfPermissive err_handler $ definitionTask instanceName >>= \case
    SkipIt ->
      pure [CommentSentence . Comment $
              "Skipping instance `" <> textP instanceName <> "' of class `" <> textP instanceClass <> "'"]

    RedefineIt def ->
      [definitionSentence def] <$ case def of
        CoqInductiveDef        _   -> editFailure   "cannot redefine an instance definition into an Inductive"
        CoqDefinitionDef       _   -> editFailure   "cannot redefine an instance definition into a Definition"
        CoqFixpointDef         _   -> editFailure   "cannot redefine an instance definition into a Fixpoint"
        CoqInstanceDef         _   -> pure ()
        CoqAxiomDef            _   -> editFailure   "cannot redefine an instance definition into an Axiom"
        CoqAssertionDef        apf -> editFailure $ "cannot redefine an instance definition into " ++ anAssertionVariety apf

    AxiomatizeIt axMode ->
      lookupClassDefn instanceClass >>= \case
        Just (ClassDefinition _ _ _ methods)
          | null methods ->
            pure [ InstanceSentence $ InstanceDefinition instanceName [] instanceHead [] Nothing]
          | otherwise ->
            pure [ InstanceSentence $ InstanceProof instanceName [] instanceHead $ ProofAdmitted ""]
        Nothing -> case axMode of
          GeneralAxiomatize  -> pure []
          SpecificAxiomatize -> no_class_instance_error instanceClass instanceName

    TranslateIt -> do
      cid_binds_map <- bindsToMap (map unLoc $ bagToList cid_binds)
      cid_types_map <- clsInstFamiliesToMap cid_tyfam_insts

      let (binds', classTy) = decomposeForall instanceHead

      -- decomposeClassTy can fail, so run it in the monad so that
      -- failure will be caught and cause the instance to be skipped
      (className, instTy) <- either convUnsupportedHere pure $ decomposeClassTy classTy
      
      _inst@ConvertedInstance{..} <- lookupInstance instTy className env
      let binds = convertedInstanceBinds ++ filter (\b -> binderGeneralizability b == Generalizable) binds'

      -- Get the methods of this class (this should already exclude skipped ones)
      (classMethods, classArgs) <- lookupClassDefn className >>= \case
        Just (ClassDefinition _ args _ sigs) -> pure (map fst sigs, args)
        _ -> no_class_instance_error className instanceName

      -- Associated types for this class
      classTypes <- fromMaybe mempty <$> lookupClassTypes className

      classDefaults <- fromMaybe M.empty <$> lookupDefaultMethods className

      let localNameFor :: Qualid -> Qualid
          localNameFor meth = qualidMapBase (<> ("_" <> qualidBase meth)) instanceName

      -- In the translation of meth1, we want all _other_ methods to be renamed
      -- to the concrete methods of the current instance (because type class methods
      -- usually refer to each other).
      -- We don’t do this for the current method (because type class methods are usually
      -- not recursive.)
      -- This is a heuristic, and the user can override it using `rewrite` rules.
      let envFor :: Qualid -> r -> r
          envFor meth = appEndo $ foldMap Endo
            [ edits.renamings.at (NamespacedIdent ns m) ?~ localNameFor m
            | m <- classMethods
            , m /= meth
            , let ns = if m `elem` classTypes then TypeNS else ExprNS]

      let allLocalNames = M.fromList $  [ (m, Qualid (localNameFor m)) | m <- classMethods ]

      let quantify sub meth body = (maybeFun ?? body) . subst sub <$> getImplicitBindersForClassMember className meth

      -- For each method, look for
      --  * explicit definitions
      --  * default definitions
      -- in that order
      methodSentences <- forM classMethods $ \meth -> do
        let localMeth = localNameFor meth

        methBody <- case (M.lookup meth cid_binds_map, M.lookup meth cid_types_map, M.lookup meth classDefaults) of
          (Just bind, _, _) ->
            local (envFor meth) $ convertMethodBinding localMeth bind >>= \case
              ConvertedDefinitionBinding cd ->
                pure . CM_Defined CL_Term $ maybeFun (cd^.convDefArgs) (cd^.convDefBody)
              ConvertedPatternBinding {} ->
                throwProgramError "pattern bindings in instances"
              ConvertedAxiomBinding {} ->
                throwProgramError "axiom bindings in instances"
              RedefinedBinding _ def ->
                CM_Renamed (definitionSentence def) <$ case def of
                  CoqInductiveDef        _   -> editFailure   "cannot redefine an instance method definition into an Inductive"
                  CoqDefinitionDef       _   -> pure ()
                  CoqFixpointDef         _   -> pure ()
                  CoqInstanceDef         _   -> editFailure   "cannot redefine an instance method definition into an Instance"
                  CoqAxiomDef            _   -> pure ()
                  CoqAssertionDef        apf -> editFailure $ "cannot redefine an instance method definition into " ++ anAssertionVariety apf
              SkippedBinding _ -> throwProgramError "skipping binding in instance"

          (Nothing, Just assoc, _) ->
            let convertedType = withCurrentDefinition meth $ convertHsType assoc in

            CM_Defined CL_Type <$> local (envFor meth) convertedType
            -- TODO: Permit rewriting or renaming or similar here

          (Nothing, Nothing, Just term) ->
            let extraSubst
                  | meth `elem` classTypes =
                    let names = foldMap (^..binderIdents) . filter (\b -> binderExplicitness b == Explicit)
                    in M.fromList $ zip (names classArgs) [instTy]
                  | otherwise =
                    mempty
            in -- In the body of the default definition, make methods names
               -- refer to their local version
               -- TODO: Associated type defaults should remember that they're types
               pure . CM_Defined CL_Term $ subst (allLocalNames <> extraSubst) term

          (Nothing, Nothing, Nothing) ->
            throwProgramError $ "The method `" <> showP meth <> "' has no definition and no default definition"

        case methBody of
          CM_Renamed renamed ->
            pure renamed
          CM_Defined level body    -> do

            let (params, sub') = (case level of
                                    CL_Term -> makeInstanceMethodSubst
                                    CL_Type -> makeAssociatedTypeSubst) binds

            -- Why the nested substitution?  The only place the per-instance variable name
            -- can show up is in the specific instance type!  It can't show up in the
            -- signature of the method, that's the whole point
            let sub = (fmap $ subst sub') convertedInstanceSubst
            
            -- We've converted the method, now sentenceify it
            ty    <- makeTy sub className meth
            -- Expand GHC.Prim.coerce into explicit newtype wrapping/unwrapping
            -- to avoid Coq Coercible/Unpeel resolution loops
            expandedBody <- case level of
              CL_Term -> expandCoerce [] (Just ty) body
              _       -> pure body
            qbody <- quantify sub meth $ substTy sub' expandedBody
            pure . DefinitionSentence $ DefinitionDef Local
                                                      localMeth
                                                      (subst allLocalNames <$> params)
                                                      (Just $ subst allLocalNames ty)
                                                      qbody
                                                      NotExistingClass

      let instHeadTy = appList (Qualid className)
            (PosArg <$> filterVisibleVars convertedInstanceClass convertedInstanceTypes)
      instance_sentence <- view (edits.simpleClasses.contains className) >>= \case
        True  -> do
          methods <- traverse (\m -> (m,) <$> quantify M.empty m (Qualid $ localNameFor m)) classMethods
          pure $ ProgramSentence
                   (InstanceSentence $ InstanceDefinition instanceName binds instHeadTy methods Nothing)
                   Nothing
        False -> do
          -- Assemble the actual record
          instRHS <- fmap Record $ forM classMethods $ \m -> do
                       method_body <- subst convertedInstanceSubst $ quantify M.empty m $ Qualid (localNameFor m)
                       return (qualidMapBase (<> "__") m, method_body)
          -- TODO: This should probably be created with 'gensym'/'genqid', but then I
          -- have to be within a 'LocalConvMonad' and then I have to think exactly about
          -- what that means here.
          let cont_name :: Qualid
              cont_name = "k__"
          -- cont_name <- genqid "k"
          let instBody = Fun (ExplicitBinder UnderscoreName NE.:| [ExplicitBinder (Ident cont_name)])
                             (App1 (Qualid cont_name) instRHS)
          let instTerm = InstanceTerm instanceName binds instHeadTy instBody Nothing

          pure $ ProgramSentence (InstanceSentence instTerm) Nothing

      pure $ methodSentences ++ [instance_sentence]
#if __GLASGOW_HASKELL__ >= 806
convertClsInstDecl _env (XClsInstDecl v) = noExtCon v
#endif

--------------------------------------------------------------------------------

convertClsInstDecls :: ConversionMonad r m => ConvertedInstanceEnv -> [ClsInstDecl GhcRn] -> m [Sentence]
convertClsInstDecls env = foldTraverse (convertClsInstDecl env)

-- Look up the type class variable and the type of the class member without
-- postprocessing.
lookupInstanceMethodTy :: ConversionMonad r m => Qualid -> Qualid -> m Term
lookupInstanceMethodTy className memberName =
  lookupClassDefn className >>= \case
    Just (ClassDefinition _ _ _ sigs) ->
      case lookup memberName sigs of
        Just sigType -> pure sigType
        Nothing      -> throwProgramError $ "Cannot find signature for " ++ quote_qualid memberName
    _ -> no_class_method_error className memberName

makeTy :: ConversionMonad r m => M.Map Qualid Term -> Qualid -> Qualid -> m Term
makeTy instSub className memberName = subst instSub <$> lookupInstanceMethodTy className memberName

makeAssociatedTypeSubst :: [Binder] -> ([Binder], M.Map Qualid Term)
makeAssociatedTypeSubst params = (params, M.empty)

-- lookup the type of the class member
-- add extra quantifiers from the class & instance definitions
makeInstanceMethodSubst :: [Binder] -> ([Binder], M.Map Qualid Term)
makeInstanceMethodSubst params = 
  -- GOAL: Consider
  -- @
  --     class Functor f where
  --       fmap :: (a -> b) -> f a -> f b
  --     instance Functor (Either a) where fmap = ...
  -- @
  -- When desugared naïvely into Coq, this will result in a term with type
  -- @
  --     forall {a₁}, forall {a₂ b},
  --       (a₂ -> b) -> Either a₁ a₂ -> Either a₁ b
  -- @
  -- Except without the subscripts!  So we have to rename either
  -- the per-instance variables (here, @a₁@) or the type class
  -- method variables (here, @a₂@ and @b@).  We pick the
  -- per-instance variables, and rename @a₁@ to @inst_a₁@.
  --
  -- ASSUMPTION: type variables don't show up in terms.  Broken
  -- by ScopedTypeVariables.
  let renameInst UnderscoreName =
        pure UnderscoreName
      renameInst (Ident x) =
        let inst_x = qualidMapBase ("inst_" <>) x
        in Ident inst_x <$ modify' (M.insert x (Qualid inst_x))

      sub ty = gets (($ ty) . subst)

      (instBnds, instSubst) = (runState ?? M.empty) $ for params $ \case
        ExplicitBinder  x      -> ExplicitBinder  <$> renameInst x
        ImplicitBinders xs     -> ImplicitBinders <$> traverse renameInst xs
        Typed       g ei xs ty -> Typed       g ei <$> traverse renameInst xs <*> sub ty
        Generalized ei tm      -> Generalized   ei <$> sub tm in
  (instBnds, instSubst)

-- from "instance C ty where" access C and ty
-- TODO: multiparameter type classes   "instance C t1 t2 where"
--       instances with contexts       "instance C a => C (Maybe a) where"
decomposeClassTy :: Term -> Either String (Qualid, Term)
decomposeClassTy (App1 (Qualid cn) a) = Right (cn, normalizeType a)
decomposeClassTy ty                   =  Left $ "type class instance head `" ++ showP ty ++ "'"

decomposeForall :: Term -> ([Binder], Term)
decomposeForall (Forall bnds ty) = first (NE.toList bnds ++) (decomposeForall ty)
decomposeForall t                = ([], t)
