{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP, StandaloneDeriving, DeriveAnyClass #-}

module HsToCoq.Util.GHC.Module (
  module Module, ModuleData(..),
  moduleNameText, mkModuleNameT,
  modName, modExports, modDetails) where

import Module

import Data.Text (Text)
import qualified Data.Text as T

import qualified GHC
import HscTypes (ModDetails(..), emptyModDetails)

import Control.Lens

-- Note: the names in the list of module exports are from before any renaming
-- has occurred.
data ModuleData = ModuleData { _modName     :: ModuleName
                             , _modExports  :: [GHC.Name]
                             , _modDetails  :: ModDetails
                             } 
makeLenses ''ModuleData

instance Semigroup ModDetails where
#if __GLASGOW_HASKELL__ >= 806
  ModDetails e1 t1 i1 f1 r1 a1 c1 <> ModDetails e2 t2 i2 f2 r2 a2 c2 =
    -- md_vect_info is discarded
    ModDetails (e1 <> e2) (t1 <> t2) (i1 <> i2) (f1 <> f2) (r1 <> r2) (a1 <> a2) (c1 <> c2)
#else
  ModDetails e1 t1 i1 f1 r1 a1 v1 c1 <> ModDetails e2 t2 i2 f2 r2 a2 _v2 c2 =
    -- md_vect_info is discarded
    ModDetails (e1 <> e2) (t1 <> t2) (i1 <> i2) (f1 <> f2) (r1 <> r2) (a1 <> a2) v1 (c1 <> c2)
#endif

instance Monoid ModDetails where
  mempty = emptyModDetails

instance Show ModuleName where
  showsPrec p mod = showParen (p >= 11)
                  $ showString "ModuleName " . showsPrec 11 (moduleNameString mod)

-- should this have ModuleData as a parameter instead of ModuleName?
moduleNameText :: ModuleName -> Text
moduleNameText = T.pack . moduleNameString

mkModuleNameT :: Text -> ModuleName
mkModuleNameT = mkModuleName . T.unpack
