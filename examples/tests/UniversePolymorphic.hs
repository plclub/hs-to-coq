module UniversePolymorphic where

data MyList a = Nil | Cons a (MyList a)

data Pair a b = MkPair a b
