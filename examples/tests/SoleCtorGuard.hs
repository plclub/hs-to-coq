module SoleCtorGuard where

data Single = MkSingle Bool Bool
data Nested = MkNested Single
data Choice = ChoiceA Bool | ChoiceB Bool

single :: Single -> Bool
single s | MkSingle b _ <- s = b
single _ = False

nested :: Nested -> Bool
nested n | MkNested (MkSingle b _) <- n = b
nested _ = False

choice :: Choice -> Bool
choice c | ChoiceA b <- c = b
choice _ = False

inCase :: Maybe Single -> Bool
inCase mx = case mx of
  Just s | MkSingle b _ <- s -> b
  _ -> False

empty :: [Bool] -> Bool
empty xs | [] <- xs = True
empty _ = False

data Box = MkBox Bool

unbox :: Box -> Bool
unbox box | MkBox value <- box = value
          | otherwise = False

nestedGuard :: (Bool, Box) -> Bool
nestedGuard input | (True, MkBox value) <- input = value
                  | otherwise = False
