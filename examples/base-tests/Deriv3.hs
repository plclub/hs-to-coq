module Deriv3 where

-- The same as the last example in Deriv, but without proper edit
-- see [https://github.com/antalsz/hs-to-rocq/issues/176]
data F a = G a a deriving (Eq, Ord)
