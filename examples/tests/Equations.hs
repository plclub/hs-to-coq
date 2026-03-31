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

-- Nested let: simple let y=x is outermost so no where clause is extracted;
-- the pattern-matching helper stays inline as a let binding
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
