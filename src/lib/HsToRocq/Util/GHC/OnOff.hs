{-# LANGUAGE TypeSynonymInstances, PatternSynonyms, ViewPatterns,
             TemplateHaskell, CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module HsToRocq.Util.GHC.OnOff {-# WARNING "Do we really need `OnOff`?" #-} (
  OnOff, pattern On, pattern Off,
  onOffToEither, eitherToOnOff
  ) where

import DynFlags

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

#define TYPE_QUOTES ''
#define VAL_QUOTES  '

#define DYN_NAME(q,name) \
  case q DynFlags of Name _ nf -> Name (OccName name) nf

type OnOff = $(conT $ DYN_NAME(TYPE_QUOTES,"OnOff"))

pattern On  :: a -> OnOff a
pattern Off :: a -> OnOff a

pattern On  a <- (onOffToEither -> Left  a) where On  a = eitherToOnOff (Left  a)
pattern Off a <- (onOffToEither -> Right a) where Off a = eitherToOnOff (Right a)

onOffToEither :: OnOff a -> Either a a
onOffToEither $((conP $ DYN_NAME(VAL_QUOTES,"On"))  [varP $ mkName "a"]) = Left  a
onOffToEither $((conP $ DYN_NAME(VAL_QUOTES,"Off")) [varP $ mkName "a"]) = Right a

eitherToOnOff :: Either a a -> OnOff a
eitherToOnOff (Left  a) = $(conE $ DYN_NAME(VAL_QUOTES,"On"))  a
eitherToOnOff (Right a) = $(conE $ DYN_NAME(VAL_QUOTES,"Off")) a

instance Show a => Show (OnOff a) where
  show oo = case show (onOffToEither oo) of
              'L':'e':'f':'t':s     -> "On"  ++ s
              'R':'i':'g':'h':'t':s -> "Off" ++ s
              s                     -> "?OnOff? " ++ s
