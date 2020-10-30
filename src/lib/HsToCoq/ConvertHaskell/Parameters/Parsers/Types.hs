{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | The parser monad and stateful operations specific to parsing edits.
module HsToCoq.ConvertHaskell.Parameters.Parsers.Types where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Text (Text)

import Control.Monad.Parse (ParseError)
import Control.Monad.State (MonadState)

import HsToCoq.Util.Has
import HsToCoq.Coq.Gallina (ModuleIdent, AccessIdent, Qualid(..))
import HsToCoq.ConvertHaskell.Parameters.Parsers.Lexing (Lexing, runLexing)

newtype AliasedModules = AliasedModules
  { aliasedModules :: Map ModuleIdent ModuleIdent
  } deriving Show

type Parser = Lexing AliasedModules

type MonadParser s m = (MonadState s m, Has s AliasedModules)

runParser :: Parser a -> Text -> Either [ParseError] a
runParser p = runLexing p (AliasedModules M.empty)

newAliasedModule :: ModuleIdent -> ModuleIdent -> AliasedModules -> AliasedModules
newAliasedModule alias orig s =
  s { aliasedModules = M.insert alias orig (aliasedModules s) }

aliasModule ::
  MonadParser s m => (ModuleIdent -> ModuleIdent -> a) -> ModuleIdent -> ModuleIdent -> m a
aliasModule mkEdit alias orig = do
  modifyPart (newAliasedModule alias orig)
  pure (mkEdit alias orig)

expandModuleIdent :: MonadParser s m => ModuleIdent -> m ModuleIdent
expandModuleIdent mod = do
  s <- getPart
  pure (M.findWithDefault mod mod (aliasedModules s))

mkQualid :: MonadParser s m => ModuleIdent -> AccessIdent -> m Qualid
mkQualid mod name = do
  mod' <- expandModuleIdent mod
  pure (Qualified mod' name)
