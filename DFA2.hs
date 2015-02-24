{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}

module DFA2 where
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
-- import Control.Lens hiding (elements)
-- import Control.Lens.Prism

-- We actually don't need the contrustors, or do we?
data Sym a = SymT Bool
    deriving (Typeable)
data Alt x y = LeftT x | RightT y | Both x y
    deriving (Typeable)
data Cut x y = CutT x y
    deriving (Typeable)
data Seq x y = SeqT x y
    deriving (Typeable)
data Not x = NotT
    deriving (Typeable)
data Rep x = RepT [x]
    deriving (Typeable)
data Eps x = EpsT x
    deriving (Typeable)
data Nil x = NilT
    deriving (Typeable)

data Re a x where
    -- Ranges of letters.  Nothing stands for .
    -- TODO: Add character classes later.
    Sym :: Maybe [a] -> Re a (Sym a)
    -- Alternative, |
    Alt :: Re a x -> Re a y -> Re a (Alt x y)
    -- Intersection
    Cut :: Re a x -> Re a y -> Re a (Cut x y)
    -- Sequencing
    Seq :: Re a x -> Re a y -> Re a (Seq x y)
    -- Repetition, Kleene Star *
    Rep :: Re a x -> Re a (Rep x)
    -- Plus :: Re a x -> Re a (NonEmptyList x)
    -- Complement
    Not :: Re a x -> Re a (Not x)
    -- Match empty string
    Eps :: x -> Re a (Eps x)
    -- Match no string
    Nil :: Re a (Nil x) 
    FMap :: (x -> y) -> Re a x -> Re a y
    deriving (Typeable)

pass :: Ord a => Re a x -> a -> x -> x
pass (Sym x) a (SymT False) = (SymT False)

