{-# LANGUAGE NoImplicitPrelude #-}
module GHC.Internal.Exception.Context where

import GHC.Types ()

data ExceptionContext = ExceptionContext

emptyExceptionContext :: ExceptionContext
emptyExceptionContext = ExceptionContext
