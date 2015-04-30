{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, OverlappingInstances #-}

module Result (Result(..)) where
import Types
import qualified Data.Set as Set
import Data.Set (Set)

import Data.Monoid
import Data.Ord

data Result x where
    Sym :: Char -> Result Sym
    Alt2 :: Result x -> Result y -> Result (Alt x y)
    AltL :: Result x -> Result (Alt x y)
    AltR :: Result y -> Result (Alt x y)
    Cut :: Result x -> Result y -> Result (Cut x y)
    Seq :: Result x -> Result y -> Result (Seq x y)
    Rep :: [Result x] -> Result (Rep x)
    -- Perhaps only for SymError?
    SymError :: SymError -> Result SymError

instance Eq (Result x) where
    (Sym x) == (Sym y) = x == y
    (AltL x) == (AltL y) = x == y
    (AltR x) == (AltR y) = x == y
    (Alt2 xl xr) == (Alt2 yl yr) = (xl, xr) == (yl, yr)
    (Cut xl xr) == (Cut yl yr) = (xl, xr) == (yl, yr)
    (Seq xl xr) == (Seq yl yr) = (xl, xr) == (yl, yr)
    (Rep x) == (Rep y) = x == y
    (SymError x) == (SymError y) = x == y
    _ == _ = False

reduce :: Result (Alt x y) -> (Maybe (Result x), Maybe (Result y))
reduce (AltL x) = (Just x, Nothing)
reduce (AltR y) = (Nothing, Just y)
reduce (Alt2 x y) = (Just x, Just y)

instance Ord (Result x) where
    compare (Sym x) (Sym y) = compare x y
    -- a bit ugly, but I guess that's the syntax..
    compare l@(AltL _) r = comparing reduce l r
    compare l@(AltR _) r = comparing reduce l r
    compare l@(Alt2 _ _) r = comparing reduce l r
    compare (Cut xl xr) (Cut yl yr) = compare (xl, xr) (yl, yr)
    compare (Seq xl xr) (Seq yl yr) = compare (xl, xr) (yl, yr)
    -- Watch out.
    compare (Rep x) (Rep y) = compare x y
    compare (SymError x) (SymError y) = compare x y
