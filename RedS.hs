{-# LANGUAGE GADTs,TupleSections #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
import Data.List
import Data.Typeable
import Data.Data
import Control.Applicative
import Test.QuickCheck

-- Add character classes later.
data Re a x y where
    Cut :: Re a x x' -> Re a y y' -> Re a (x,y) (x',y')
    -- Match empty string
    Eps :: x' -> Re a x x'
    -- Match no string
    Nil :: Re a x x'
    -- This ain't enough.
    FMap :: (x' -> y') -> Re a x x' -> Re a (FMap x) y'
    deriving (Typeable)

data Not x
data FMap x
data FMap2 x y

-- How to do Not and Eps and Nil?

-- deriving instance Show (ReX a x)
-- deriving instance Eq (ReX a x)
-- deriving instance Ord (ReX a x)

show' :: Re Char x x' -> String
show' re = case re of
    Cut a b -> show' a ++ "&" ++ show' b
    Eps _ -> "ε"
    Nil -> "∅"
    FMap _ a -> show' a -- Not great.

-- Something wrong here.
n :: Re a x y -> Bool
n (Cut a b) = n a && n b
n (Eps _) = True
n Nil = False
n (FMap _ x) = n x

n' :: Re a x x' -> Maybe x'
n' (Cut a b) = liftA2 (,) (n' a) (n' b)
n' (Eps x) = Just x
n' Nil = Nothing
n' (FMap f x) = fmap f (n' x)

v' :: Re a x x' -> Re a x x'
v' = maybe Nil Eps . n'

-- float up FMap?
{-
a :: Re a x -> (y -> x, Re a y)
a (FMap f x) = let (g, y) = a x in (f . g, y)
a (Sym x) = (id, Sym x)
a (Alt x y) = let (gl, x') = a x
                  (gr, y') = a y
              in (_ gl gr, Alt x' y')
-}

simplify,s :: Eq a => Re a x x' -> Re a x x'
s = simplify
simplify re = case re of
    Cut Nil _ -> Nil
    Cut _ Nil -> Nil
    Eps x -> Eps x
    Nil -> Nil
    FMap f (FMap g x) -> FMap (f . g) (s x)
--    FMap f x -> FMap f (s x)
    -- Cut Sym Sym would be useful.
    Cut x y ->  Cut (s x) (s y)
-- simplify = foldRe1 simplify1

-- type C2 a = Re a x -> Re a -> Re a
-- type C1 a x = Re a x -> Re a x
-- foldRe1 :: C1 a x -> C1 a x
-- -- Needs more typing magic!
{-
foldRe1 s =
    let f re = s $ case re of
            Sym x -> Sym x
            (Alt a b) -> Alt (f a) (f b)
            (Cut a b) -> Cut (f a) (f b)
            Eps -> Eps
            Nil -> Nil
    in f
-}

d :: Eq a => a -> Re a x x' -> Re a x x'
d c (Cut a b) = Cut (d c a) (d c b)
d _ (Eps _) = Nil
d _ Nil = Nil
d c (FMap f x) = FMap f (d c x)

-- Pass to float up FMaps? --- especially needed for minimization.

-- Ha, this is almost trivial!

ds c = simplify . d c

-- -- This should not be possible to define sensibly.
-- instance Monad (Re a) where

-- flapping' :: Re Char


-- match :: Eq a => Re a -> [a] -> Bool
match re = n . foldl (flip d) re
-- sym :: [a] -> Re a

-- str :: [a] -> Re a

pp = putStrLn . show'

main = do
    return ()

