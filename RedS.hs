{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
module Main where
-- import Data.Foldable hiding (fold, concatMap, foldr, elem, foldl, mapM_)
import Prelude hiding (sequence, mapM)
import Data.List (sort)
import Data.Monoid
import Data.Maybe (isJust)
import qualified Data.Set as Set
import Data.Ord
import Data.Typeable
import Control.Applicative
-- TODO: Look into lenses.
import Test.QuickCheck
import Test.QuickCheck.Function
import Test.QuickCheck.All

import Control.Arrow
import Control.Monad

import Debug.Trace (trace)

import qualified Red

data Re a x where
    -- Ranges of letters.  Nothing stands for .
    -- TODO: Add character classes later.
    Sym :: Maybe [a] -> Maybe a -> Re a a
    -- Alternative, |
    Alt :: Re a x -> Re a y -> Re a (Either x y)
    -- Intersection
    Cut :: Re a x -> Re a y -> Re a (x,y)
    -- Sequencing
    Seq :: Re a x -> Re a y -> Re a (x,y)
    -- Repetition, Kleene Star *
    Rep :: Re a x -> Re a [x]
    -- Plus :: Re a x -> Re a (NonEmptyList x)
    -- Complement
    Not :: Re a x -> Re a ()
    -- Match empty string
    Eps :: x -> Re a x
    -- Match no string
    Nil :: Re a x
    -- Do I still need FMap?
    FMap :: (x -> y) -> Re a x -> Re a y
    deriving (Typeable)

test___ = Not test___

-- Need to separate shape from computation / data?

-- Need Re a x with a zipper (actually with multiple holes)
-- d, n

-- Push pebbles, the pebbles mark which state we are in, and can also carry values.
-- The pebbles _can_ have different types, and we need to have some conversions?
-- As an optimization, it would be useful to have an isEmpty? check.

-- How to convert?  Use continuations?

-- Principle:
-- In the end, each char of input is mapped to one or more Sym leaves.
-- We are describing a bunch of paths (ie a dag) through our regex tree.

-- Given a path (from the dag) and the tree, we can zipper through the tree,
-- and generate a parse value?

-- We need explicit sharing (for the dag) to get efficency.

-- A Sym leave corresponds to a non-Eps transition, everything else we move through via Eps transitions
-- ie in between chars.


-- d :: Eq a => a -> Re a x -> Re a x
-- d c (Seq a b) = Seq (d a)
-- d' c (Seq a b) = Seq (d a) (d' (n a) a b)
-- 
-- 
-- d :: Eq a => a -> Re a x -> Re a x
-- d c (Sym Nothing) = Eps c
-- d c (Sym (Just as))
--     | c `elem` as = Eps c
--     | otherwise = Nil
-- d c (Alt a b) = Alt (d c a) (d c b)
-- d c (Cut a b) = Cut (d c a) (d c b)
-- -- This one grows.
-- d c (Seq a b) = FMap (either id id) $ Seq (d c a) b `Alt` Seq (v a) (d c b)
-- -- d c (Seq a b) = Seq (d c a) b `Alt` Seq (v a) (d c b)
-- -- This one grows.
-- d c (Rep a) = FMap (uncurry (:)) $ Seq (d c a) (Rep a)
-- -- Something like:
-- -- d c (Rep a b) = uncurry Rep (d_ c a b) `Alt` Seq (v b) (Alt Eps (Rep (a++b)))
-- d c (Not a) = Not (d c a)
-- d _ (Eps _) = Nil
-- d _ Nil = Nil
-- d c (FMap f x) = FMap f (d c x)
-- 
n' :: Re a x -> Maybe x
n' (Sym _ x) = x
n' (Alt a b) = (Left <$> n' a) <|> (Right <$> n' b)
n' (Cut a b) = liftA2 (,) (n' a) (n' b)
-- This is wrong!
-- Need to discriminate between epsilonable, and value.
n' (Seq a b) = undefined $ liftA2 (,) (n' a) (n' b)
-- Could also just always give []
n' (Rep a) = fmap (:[]) (n' a) <|> Just []
n' (Not a) = maybe (Just ()) (const Nothing) $ n' a
n' (Eps x) = Just x
n' Nil = Nothing
n' (FMap f x) = fmap f (n' x)

-- v :: Re a x -> Re a x
-- v = maybe Nil Eps . n'

main = return ()
