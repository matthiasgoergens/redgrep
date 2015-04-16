{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, OverlappingInstances #-}

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
import Data.Bifunctor.Apply

import Types

-- import Control.Lens hiding (elements)
-- import Control.Lens.Prism 



-- This is the heart of the derivative based algorithm.
-- Everything else just needs to support these operations

type SymResult = Maybe (Either Char SymError)

extract :: ReE SymResult x y -> Maybe (Either (a x) (a y))
extract = undefined

v = undefined

{-
d :: Eq a => a -> Re a x -> Re a x
d c (SymX Nothing) = EpsX c
d c (SymX (Just as))
    | c `elem` as = EpsX c
    | otherwise = NilX
d c (AltX a b) = AltX (d c a) (d c b)
d c (CutX a b) = CutX (d c a) (d c b)
-- This one grows.
-- The top-most Alt can be done by our `unionCut`
-- can and has to be.
d c (SeqX a b) = union (SeqX (d c a) b) (SeqX (v a) (d c b))
-- This one grows. -- but doesn't have to.
d c (RepX a) = undefined -- $ FMap (uncurry (:)) $ Seq (d c a) (Rep a)
-- Magic here.
d c (NotX a) = NotX (d c a)
-- Need to be able to represent Nil.
d _ (EpsX _) = NilX
d _ NilX = NilX
-- d c (FMap f x) = FMap f (d c x)
-}

-- Is this some kind of (<*>)?  If yes, than on the first argument, not the last/second.
-- Can we abstract this repeated pattern?  (Something like uniplate, or scrap your boilerplate?)
-- Oh, NotX means we need an explicit & and | (swapping them, because of DeMorgan's law.)
unionCut :: forall f g h x . (f -> g -> h) -> (f -> g -> h) -> Re f x -> Re g x -> Re h x
unionCut (*) (+) = u where
    u :: forall x . Re f x -> Re g x -> Re h x
    u (SymX x) (SymX y) = SymX $ x + y
    u (AltX x y) (AltX x' y') = AltX (u x x') (u y y')
    u (SeqX x y) (SeqX x' y') = SeqX (u x x') (u y y')
    u (CutX x y) (CutX x' y') = CutX (u x x') (u y y')
    -- NOTE: we swap (+) and (*).
    u (NotX x) (NotX x') = NotX $ unionCut (+) (*) x x'
    u (RepX x) (RepX x') = RepX $ u x x'
    -- We have a choice here.  Doesn't matter too much what we do.
    -- Left biased by default.
    u (EpsX x) (EpsX x') = EpsX $ x
    u NilX NilX = NilX

-- Or do we need BoolBefore?
union, cut :: Re BoolAfter x -> Re BoolAfter x -> Re BoolAfter x
union = unionCut (onBoolAfter (&&)) (onBoolAfter (||))
cut   = unionCut (onBoolAfter (||)) (onBoolAfter (&&))
onBoolAfter (*) (BoolAfter x) (BoolAfter y) = BoolAfter $ x * y
onBoolBefore (*) (BoolBefore x) (BoolBefore y) = BoolBefore $ x * y


main = return ()
