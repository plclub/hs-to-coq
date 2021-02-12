module Invariant(Counter, zeroCounter, inc, dec, isZero) where

    data Counter = MkC Int
        deriving Show

    zeroCounter :: Counter
    zeroCounter = MkC 0

    inc :: Counter -> Counter
    inc (MkC x) = MkC (x+1)

    dec :: Counter -> Counter
    dec (MkC x) = if x > 0 then MkC (x - 1) else MkC 0

    isZero :: Counter -> Bool
    isZero (MkC x) = x == 0

    valid :: Counter -> Bool
    valid (MkC x) = x >= 0
    
