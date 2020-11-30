{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}

-- This module is a heuristic for substituting only types

module HsToCoq.Coq.SubstTy (
  -- * Things that can be substituted
  SubstTy(..), subst1
  ) where

import           Prelude               hiding (Num)


import           Data.Map.Strict       (Map)

import           HsToCoq.Coq.Gallina
import           HsToCoq.Coq.Subst

----------------------------------------------------------------------------------------------------

-- Note: this is not capture avoiding substitution (yet!)
--
-- When it comes across an operator, it searches for its 'infixToCoq' name
-- in the map, and turns the operator application into a term application
-- if necessary.

class SubstTy t where
  substTy :: Map Qualid Term -> t -> t

instance SubstTy IndBody where
  substTy f (IndBody tyName params indicesUnivers cons) =
    IndBody tyName params indicesUnivers (map (substCon f) cons)
       where substCon f (qid,binders, Nothing) = (qid, map (subst f) binders, Nothing)
             substCon f (qid,binders, Just t)  = (qid, map (subst f) binders, Just (substTy f t))

instance SubstTy MatchItem where
  substTy f (MatchItem t oas oin) = MatchItem (substTy f t) oas oin

instance SubstTy MultPattern where
  substTy f (MultPattern pats) = MultPattern (substTy f pats)

instance SubstTy Pattern where
  substTy _f pat = pat

instance SubstTy Assumption where
  substTy f (Assumption kwd assumptions) =
    Assumption kwd (substTy f assumptions)
    -- The @kwd@ part is pro forma – there are no free variables there

instance SubstTy Assums where
  substTy f (Assums xs ty) = Assums xs (substTy f ty)

instance SubstTy Definition where
  substTy f (LetDef x args oty def) =
    LetDef x (subst f args) (substTy f oty) (substTy f def)

  substTy f (DefinitionDef isL x args oty def ex) =
    DefinitionDef isL x (subst f args) (substTy f oty) (substTy f def) ex



instance SubstTy Inductive where
  substTy _f (Inductive   _ibs _nots) = error "subst"
  substTy _f (CoInductive _cbs _nots) = error "subst"


instance SubstTy Fixpoint where
  substTy f (Fixpoint   fbs nots) = Fixpoint (substTy f fbs) (subst f nots)
  substTy f (CoFixpoint cbs nots) = CoFixpoint (substTy f cbs) (subst f nots)

instance SubstTy Order where
  substTy _f (StructOrder ident)     = StructOrder ident
  substTy f  (MeasureOrder expr rel) = MeasureOrder (substTy f expr) (substTy f rel)
  substTy f  (WFOrder rel ident)     = WFOrder      (substTy f rel)  ident

instance SubstTy Assertion where
  substTy f (Assertion kwd name args ty) = Assertion kwd name (subst f args) (substTy f ty)

instance SubstTy FixBodies where
    substTy f (FixOne b)        = FixOne  (substTy f b)
    substTy f (FixMany b neb x) = FixMany (substTy f b) (substTy f neb) x

instance SubstTy FixBody where
    substTy f (FixBody n bs ma mt t) = FixBody n (subst f bs) (substTy f ma) (subst f mt) (substTy f t)

instance SubstTy Arg where
   substTy f (PosArg t)     = PosArg (substTy f t)
   substTy f (NamedArg i t) = NamedArg i (substTy f t)

instance SubstTy Equation where
   substTy f (Equation nep t) = Equation nep (substTy f t)

instance SubstTy Term where
  substTy f  (Forall xs t) = Forall (subst f xs) (subst f t)

  substTy f  (Fun xs t) = Fun (subst f xs) (substTy f t)

  substTy f  (Fix fbs) = Fix (substTy f fbs)

  substTy f  (Cofix cbs) = Cofix (substTy f cbs)

  substTy f  (Let x args oty val body) = Let x (subst f args) (subst f oty) (substTy f val) (substTy f body)

  substTy f  (LetTuple xs oret val body) = LetTuple xs (subst f oret) (substTy f val) (substTy f body)

  substTy f  (LetTick pat def body) = LetTick (substTy f pat) (substTy f def) (substTy f body)

  substTy f  (If is c oret t fa) = If is (substTy f c) (subst f oret) (substTy f t) (substTy f fa)

  substTy f  (HasType tm ty) = HasType (substTy f tm) (subst f ty)

  substTy f  (CheckType tm ty) = CheckType (substTy f tm) (subst f ty)

  substTy f  (ToSupportType tm) = ToSupportType (substTy f tm)

  substTy f  (Arrow ty1 ty2) = Arrow (subst f ty1) (subst f ty2)

  substTy f  (App fu xs) = App (substTy f fu) (substTy f  xs)

  substTy f  (ExplicitApp qid xs) = ExplicitApp qid (substTy f  xs)

  substTy f  (InScope t scope) =  InScope (substTy f  t) scope
    -- The scope is a different sort of identifier, not a term-level variable.

  substTy f (Match items oret eqns) = Match (substTy f items) (subst f oret) (substTy f eqns)

  substTy _f x@(Qualid _qid) = x

  substTy _f x@(RawQualid _qid) = x

  substTy _f x@(Sort _sort) = x

  substTy _f x@(Num _num) = x

  substTy _f x@(String _str) = x

  substTy _f x@(HsString _str) = x

  substTy _f x@(HsChar _char) = x

  substTy _f x@Underscore = x

  substTy f (Parens t) = Parens (substTy f t)

  substTy f (Bang t) = Bang (substTy f t)

  substTy f (Record defns) = Record [ (v, subst f t) | (v,t) <- defns ]

instance (SubstTy a, Functor f) => SubstTy (f a) where
  substTy f = fmap (substTy f)
