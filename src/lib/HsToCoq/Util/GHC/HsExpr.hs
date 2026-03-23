{-# LANGUAGE CPP #-}

#include "ghc-compat.h"

module HsToCoq.Util.GHC.HsExpr (
  module HsExpr,
  isNoSyntaxExpr,
  isNoPostTcExpr,
  isGenLitString
) where

#if __GLASGOW_HASKELL__ >= 900
import GHC.Plugins
import Language.Haskell.Syntax.Expr
import GHC.Tc.Types.Evidence (HsWrapper(..))
#else
import TcEvidence (HsWrapper(..))
import FastString
#endif
#if __GLASGOW_HASKELL__ >= 810
import GHC.Hs.Lit
import GHC.Hs.Expr as HsExpr
#else
import HsLit
import HsExpr
#endif

isGenLitString :: String -> HsExpr pass -> Bool
isGenLitString str (HsLit NOEXTP (HsString _ fstr)) = fsLit str == fstr
isGenLitString _   _                          = False

-- GHC 9.x simplified SyntaxExpr to a single-field SyntaxExprRn wrapper
-- (no more syn_arg_wraps/syn_res_wrap fields), so the match is just on the
-- inner expression.
#if __GLASGOW_HASKELL__ >= 900
isNoSyntaxExpr :: SyntaxExprRn -> Bool
isNoSyntaxExpr (SyntaxExprRn expr) =
#else
isNoSyntaxExpr :: SyntaxExpr pass -> Bool
isNoSyntaxExpr SyntaxExpr{ syn_expr      = expr
                         , syn_arg_wraps = []
                         , syn_res_wrap  = WpHole } =
#endif
  isGenLitString "noSyntaxExpr" expr
isNoSyntaxExpr _ =
  False

isNoPostTcExpr :: PostTcExpr -> Bool
isNoPostTcExpr = isGenLitString "noPostTcExpr"
