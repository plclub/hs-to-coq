{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | The parser monad and stateful operations specific to parsing edits.
module HsToCoq.Edits.ParserState where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Text (Text)

import Control.Monad.Parse (ParseError)
import Control.Monad.State (MonadState)

import HsToCoq.Util.Has
import HsToCoq.Coq.Gallina (ModuleIdent, AccessIdent, Ident, Qualid(..))
import HsToCoq.Coq.Gallina.Util (identToQualid)
import HsToCoq.Edits.Lexer (Lexer, runLexer)

newtype AliasedModules = AliasedModules
  { aliasedModules :: Map ModuleIdent ModuleIdent
  } deriving Show

type Parser = Lexer AliasedModules

type MonadParser s m = (MonadState s m, Has s AliasedModules)

runParser :: Parser a -> Text -> Either [ParseError] a
runParser p = runLexer p (AliasedModules M.empty)

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

forceIdentToQualid :: MonadParser s m => Ident -> m Qualid
forceIdentToQualid x = case identToQualid x of
  Nothing -> error $ "internal error: lexer produced a malformed qualid: " ++ show x
  Just (Qualified mod name) -> mkQualid mod name
  Just q@(Bare _) -> pure q
