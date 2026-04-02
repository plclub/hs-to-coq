module Equations where

data N = Z | S N

-- Simple non-recursive pattern match
not_ :: Bool -> Bool
not_ True = False
not_ False = True

-- No pattern match: single equation with direct body
id_ :: Bool -> Bool
id_ x = x

-- Function with let binding
through :: Bool -> Bool
through x = let y = x in y

-- Multi-argument pattern match
and_ :: Bool -> Bool -> Bool
and_ True True = True
and_ _ _ = False

-- Function with where clause (local pattern-matching helper)
applyHelper :: Bool -> Bool
applyHelper x = let helper True = False
                    helper False = True
                in helper x

-- Two local let bindings: both a pattern-matching helper and a simple binding.
-- hs-to-coq's foldrM in convertLocalBinds (Expr.hs) may place a non-pattern-
-- matching let outermost; extractWheres recurses through nested lets to find
-- the pattern-matching one and extract it as a where clause.
applyAndKeep :: Bool -> Bool
applyAndKeep x = let helper True = False
                     helper False = True
                     y = x
                 in helper y

-- Recursive function with pattern matching (exercises Fix/decomposeFixpoint path)
toNat :: N -> N
toNat Z = Z
toNat (S n) = S (toNat n)

-- Recursive with nested patterns
halve :: N -> N
halve Z = Z
halve (S Z) = S Z
halve (S (S n)) = S (halve n)

-- Helper for guard test below
isZ :: N -> Bool
isZ Z = True
isZ _ = False

-- Guards: hs-to-coq converts guards to if/then/else,
-- which the equations edit emits as a single equation with the if body
clamp :: N -> N
clamp n
  | isZ n     = Z
  | otherwise = S Z

-- Guard first, then pattern match (guard on catch-all, pattern on second clause)
guardFirst :: N -> N
guardFirst n | isZ n = Z
guardFirst (S n) = n

-- Pattern match first, then guard (pattern on first clause, guard on second)
clampN :: N -> N
clampN Z = Z
clampN (S n)
  | isZ n     = S Z
  | otherwise = S (S Z)

-- Multi-argument function (exercises binder annotation for 2+ explicit args)
constN :: N -> N -> N
constN x _ = x

-- Polymorphic function (exercises implicit-binder filtering)
myId :: a -> a
myId x = x
