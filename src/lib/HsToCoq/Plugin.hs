{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf #-}

module HsToCoq.Plugin (plugin) where

import Data.Text (pack)
import Data.Word (Word64)
import Control.Monad.IO.Class
import System.IO

#if __GLASGOW_HASKELL__ >= 900
import GHC.Plugins hiding (vcat, InScope)
import qualified GHC.Utils.Outputable as Outputable
import GHC.Types.Tickish
#define Tickish GenTickish
import GHC.Tc.Utils.TcType as TcType
import GHC.Utils.Ppr (Mode(PageMode))
import GHC.Types.Unique (getKey)
#else
import GhcPlugins hiding (vcat)
import Unique
import TcType
import qualified Pretty
import qualified Outputable
#endif

import HsToCoq.Coq.Gallina hiding (Type, Let, App, Name)
import HsToCoq.Coq.Gallina.Orphans ()
import HsToCoq.Coq.Gallina.Util hiding (Var)
import HsToCoq.Coq.Pretty
import HsToCoq.PrettyPrint

#if __GLASGOW_HASKELL__ >= 806
type PluginPass = CorePluginPass
#endif

-- | A more convenient Gallina application operator
(<:) :: Term -> [Term] -> Term
n <: xs = appList n (map PosArg xs)

class ToTerm a where
    t :: a -> Term

instance ToTerm (Tickish b) where
    t _ = undefined

instance ToTerm Int where
    t n = InScope (Num (fromIntegral n)) "N"

-- GHC 9.10 changed Unique keys from Int to Word64
#if __GLASGOW_HASKELL__ >= 910
instance ToTerm Word64 where
    t n = InScope (Num (fromIntegral n)) "N"
#endif

instance ToTerm Module where
    t (Module a b) = App2 "Mk_Module" (t a) (t b)

-- GHC 9.x restructured package units: UnitId is now a newtype over
-- FastString, and the old IndefUnitId/DefiniteUnitId split became
-- GenUnit with RealUnit/VirtUnit/HoleUnit constructors.
-- Alt became a named data type (was a tuple in GHC 8.x).
#if __GLASGOW_HASKELL__ >= 900
instance ToTerm a => ToTerm (GenUnit a) where
  t (RealUnit a) = "RealUnit" <: [t a]
  t (VirtUnit a) = "VirtUnit" <: [t a]
  t HoleUnit = "HoleUnit"

instance ToTerm a => ToTerm (Definite a) where
  t (Definite a) = "Definite" <: [t a]

instance ToTerm (GenInstantiatedUnit a) where
  t _ = "GenInstantiatedUnit(..)"

instance ToTerm UnitId where
  t (UnitId a) = "UnitId" <: [t a]

instance ToTerm b => ToTerm (Alt b) where
  t (Alt x y z) = "Alt" <: [t x, t y, t z]
#else
instance ToTerm IndefUnitId where
    t _ = "default"

instance ToTerm UnitId where
    t (IndefiniteUnitId a) = "IndefiniteUnitId" <: [t a]
    t (DefiniteUnitId a)   = "DefiniteUnitId" <: [t a]
#endif

instance ToTerm DefUnitId where
    t _ = "default"

instance ToTerm ModuleName where
    t _ = "default"

instance ToTerm Type where
    t _ = "default"

instance ToTerm NameSpace where
    t _ = "default"

instance ToTerm FastString where
    t f = HsString (pack (unpackFS f))

instance ToTerm OccName where
    t o = "Mk_OccName" <: [t (occNameSpace o), t (occNameFS o)]

instance ToTerm Unique where
    t u = "MkUnique" <: [t (getKey u)]

instance ToTerm SrcSpan where
    t _ = "default"

instance ToTerm Name where
    t n = "Mk_Name"
        <: [ if | isWiredInName n  ->
                  App3 "WiredIn" (t (nameModule n)) "default"
                      (if isBuiltInSyntax n
                       then "BuiltInSyntax"
                       else "UserSyntax")
                | isExternalName n ->
                  App1 "External" (t (nameModule n))
                | isInternalName n -> "Internal"
                | isSystemName n   -> "System"
                -- All four NameSort cases above are exhaustive in GHC 9.10;
                -- the guard is kept so GHC does not warn about non-exhaustive
                -- guards, and we error rather than silently misclassify if a
                -- new NameSort is added upstream.
                | otherwise        -> error $ "ToTerm Name: unknown NameSort for " ++ Outputable.showPprUnsafe n
           , t (nameOccName n)
           , t (nameUnique n)
           , t (nameSrcSpan n)
           ]

instance ToTerm Var where
    t v | isTyVar v =
          "Mk_TyVar" <: [t a, t b, t c]
        | isTcTyVar v =
          "Mk_TcTyVar" <:
              [ t a
              , t b
              , t c
              , t (tcTyVarDetails v)
              ]
        | isId v =
          "Mk_Id" <:
              [ t a
              , t b
              , t c
              , if isGlobalId v
                then "GlobalId"
                else "LocalId" <: [if isExportedId v
                                   then "Exported"
                                   else "NotExported"]
              , t (idDetails v)
              , t (idInfo v) ]
        | otherwise = error "What kind of Var is that?"
      where
        a = varName v
        b = getKey (getUnique v)
        c = varType v

instance ToTerm Coercion where
    t _ = "default"

instance ToTerm AltCon where
    t _ = "default"

instance ToTerm Literal where
    t _ = "default"

instance ToTerm IdInfo where
    t _ = "default"

instance ToTerm IdDetails where
    t _ = "default"

instance ToTerm TcType.TcTyVarDetails where
    t _ = "default"

instance (ToTerm a, ToTerm b) => ToTerm (a, b) where
    t (x, y) = App2 "pair" (t x) (t y)

instance (ToTerm a, ToTerm b, ToTerm c) => ToTerm (a, b, c) where
    t (x, y, z) = App3 "pair3" (t x) (t y) (t z)

instance ToTerm b => ToTerm (Expr b) where
  t (Var n)        = App1 "Mk_Var" (t n)
  t (Lit l)        = App1 "Lit" (t l)
  t (App e a)      = App2 "App" (t e) (t a)
  t (Lam a e)      = App2 "Lam" (t a) (t e)
  t (Let n e)      = App2 "Let" (t n) (t e)
  t (Case e n u l) = appList "Case" [PosArg (t e), PosArg (t n), PosArg (t u), PosArg (t l)]
  t (Cast e u)     = App2 "Cast" (t e) (t u)
  t (Tick i e)     = App2 "Tick" (t i) (t e)
  t (Type u)       = App1 "Type_" (t u)
  t (Coercion u)   = App1 "Coercion" (t u)

instance ToTerm b => ToTerm (Bind b) where
    t (NonRec n e) = App2 "NonRec" (t n) (t e)
    t (Rec xs)     = App1 "Rec" (t xs)

instance ToTerm a => ToTerm [a] where
    t [] = "nil"
    t (x : xs) = App2 "cons" (t x) (t xs)

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ xs = return $ pass : xs
  where pass = CoreDoPluginPass "GHC.Proof" proofPass

proofPass :: PluginPass -- ModGuts -> CoreM ModGuts
proofPass guts@ModGuts {..} = do
    dflags <- getDynFlags
    liftIO $ withFile coq WriteMode $ \h -> do
#if __GLASGOW_HASKELL__ >= 900
      let ctx = initSDocContext dflags defaultDumpStyle
      printSDocLn ctx (PageMode False) h $
#else
      printSDocLn PageMode dflags h (defaultDumpStyle dflags) $
#endif
        Outputable.vcat ["(*", Outputable.ppr mg_binds, "*)"]
      hPrettyPrint h $ vcat (map renderGallina mod)
    return guts
  where
    name = moduleNameSlashes (moduleName mg_module)
    coq  = name ++ ".v"

    mod :: [Sentence]
    mod = [ ModuleSentence (Require Nothing (Just Import) ["Core"])
          , ModuleSentence (Require Nothing (Just Import) ["Name"])
          , ModuleSentence (Require Nothing (Just Import) ["OccName"])
          , ModuleSentence (Require Nothing (Just Import) ["Module"])
          , ModuleSentence (Require Nothing (Just Import) ["Unique"])
          , ModuleSentence (Require Nothing (Just Import) ["GHC.Tuple"])
          , ModuleSentence (Require Nothing (Just Import) ["GHC.Err"])
          , ModuleSentence (Require Nothing (Just Import) ["Coq.NArith.BinNat"])
          , DefinitionSentence
              (DefinitionDef Global "program" []
                 (Just (Qualid "CoreProgram")) body NotExistingClass)                  
          ]

    body :: Term
    body = t mg_binds

hPrettyPrint :: MonadIO m => Handle -> Doc -> m ()
hPrettyPrint h = liftIO . displayIO h . renderPretty 0.67 120
