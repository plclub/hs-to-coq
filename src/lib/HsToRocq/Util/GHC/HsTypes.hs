{-# LANGUAGE CPP #-}

module HsToRocq.Util.GHC.HsTypes (
  module HsTypes,
  viewHsTyVar, viewLHsTyVar,
  selectorFieldOcc_, fieldOcc,
  noExtCon
) where

#if __GLASGOW_HASKELL__ >= 806 && __GLASGOW_HASKELL__ < 810
import GHC.Stack (HasCallStack)
#endif
#if __GLASGOW_HASKELL__ >= 900
import GHC.Plugins
import GHC.Hs.Type as HsTypes
import GHC.Hs.Extension (GhcPass, GhcRn)
import Language.Haskell.Syntax.Extension (IdP, XRec, DataConCantHappen, dataConCantHappen)
#else
#if __GLASGOW_HASKELL__ >= 810
import GHC.Hs.Extension
import GHC.Hs.Types as HsTypes
#else
import HsExtension
import HsTypes
#endif
import RdrName (RdrName)
import Name (Name)
import SrcLoc
#endif

#if __GLASGOW_HASKELL__ >= 900
viewHsTyVar :: HsType (GhcPass pass) -> Maybe (IdP (GhcPass pass))
viewLHsTyVar :: LHsType (GhcPass pass) -> Maybe (IdP (GhcPass pass))
#else
viewHsTyVar :: HsType pass -> Maybe (IdP pass)
viewLHsTyVar :: LHsType pass -> Maybe (IdP pass)
#endif
#if __GLASGOW_HASKELL__ >= 806
viewHsTyVar (HsTyVar _ _ (L _ name))                  = Just name
#else
viewHsTyVar (HsTyVar _ (L _ name))                    = Just name
viewHsTyVar (HsAppsTy [L _ (HsAppInfix  (L _ name))]) = Just name
viewHsTyVar (HsAppsTy [L _ (HsAppPrefix lty)])        = viewLHsTyVar lty
#endif
viewHsTyVar _                                         = Nothing

viewLHsTyVar = viewHsTyVar . unLoc

-- Compatibility shim for FieldOcc (the fields were flipped since GHC 8.6)
#if __GLASGOW_HASKELL__ >= 806
selectorFieldOcc_ :: FieldOcc GhcRn -> Name
selectorFieldOcc_ (FieldOcc n _) = n
#if __GLASGOW_HASKELL__ < 900
selectorFieldOcc_ (XFieldOcc v) = noExtCon v
#endif

fieldOcc :: XRec GhcRn RdrName -> Name -> FieldOcc GhcRn
fieldOcc r n = FieldOcc n r

-- GHC 9.x replaced NoExtCon with DataConCantHappen (an empty type used
-- in "Trees That Grow" extension points that should never be reached).
#if __GLASGOW_HASKELL__ >= 900
noExtCon :: HasCallStack => DataConCantHappen -> a
noExtCon = dataConCantHappen
#elif __GLASGOW_HASKELL__ < 810
noExtCon :: HasCallStack => NoExt -> a
noExtCon _ = error "cannot happen"
#endif
#else
selectorFieldOcc_ :: FieldOcc GhcRn -> Name
selectorFieldOcc_ (FieldOcc _ n) = n

fieldOcc :: Located RdrName -> Name -> FieldOcc GhcRn
fieldOcc = FieldOcc

noExtCon :: ()  -- dummy to not have to put a CPP conditional in the export list
noExtCon = ()
#endif
