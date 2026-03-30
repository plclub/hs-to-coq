module UniversePolymorphic where

data MyList a = Nil | Cons a (MyList a)

data Pair a b = MkPair a b

data Tree a = Leaf a | Node (Tree a) (Tree a)

data Either_ a b = Left_ a | Right_ b
