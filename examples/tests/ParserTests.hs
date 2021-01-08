module ParserTests (Foo(..), Test(..)) where

class C a where
  c :: a -> a

a1 :: C a => a -> a
a1 = c

a2 :: (a -> b) -> a -> b
a2 x = x


-- For testing the parsing of the let-tick syntax in edit files:
data Foo = MkFoo
data Test = MkTest Foo
