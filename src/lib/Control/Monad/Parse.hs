module Control.Monad.Parse (
  -- * The 'MonadParse' type class
  MonadParse(..),
  -- * The 'Parse' monad
  P.Parse, P.runParse, P.evalParse,
  -- * The 'ParseT' monad transformer
  P.ParseT(..), P.runParseT, P.evalParseT,
  -- * Derived 'ParseT' operations
  parseToken, parseCharTokenLookahead,
  -- ** Lower-level operations
  parseChar, parseChars,
  -- * Errors
  P.Location(..), P.ParseError(..), P.prettyParseError,
) where

import qualified Control.Monad.Trans.Parse as P
import Control.Monad.Parse.Class
