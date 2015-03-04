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

data Sym a where
    Sym :: Maybe [a] -> Sym a
    deriving (Typeable, Show, Eq, Ord)
data Alt x y where
    Alt :: x -> y -> Alt x y
    deriving (Typeable, Show, Eq, Ord)
data Cut x y where
     Cut :: x -> y -> Cut x y
    deriving (Typeable, Show, Eq, Ord)
data Seq x y where
    Seq :: x -> y -> Seq x y
    deriving (Typeable, Show, Eq, Ord)
data Not x where
    Not :: x -> Not x
    deriving (Typeable, Show, Eq, Ord)
data Rep x where
    Rep :: x -> Rep x
    deriving (Typeable, Show, Eq, Ord)
data Eps x where
    Eps :: x -> Eps x
    deriving (Typeable, Show, Eq, Ord)
data Nil where
    Nil :: Nil
    deriving (Typeable, Show, Eq, Ord)

data FMap x y where
    FMap :: FMap (x -> y) y
    deriving (Typeable)

data Re f x where
    -- Ranges of letters.  Nothing stands for .
    -- TODO: Add character classes later.
    SymX :: f -> Re f (Sym x)
    -- Alternative, |
    AltX :: Re f x -> Re f y -> Re f (Alt x y)
    -- Intersection
    CutX :: Re f x -> Re f y -> Re f (Cut x y)
    -- Sequencing
    SeqX :: Re f x -> Re f y -> Re f (Seq x y)
    -- Repetition, Kleene Star *
    RepX :: Re f x -> Re f (Rep x)
    -- Plus :: Re x -> Re (NonEmptyList x)
    -- Complement
    NotX :: Re f x -> Re f (Not x)
    -- Match empty string
    EpsX :: x -> Re f (Eps x)
    -- Match no string
    NilX :: Re f Nil 
    -- -- Do we need something like the lens trick?
    -- This might not work!
    FMapX :: (x -> y) -> Re f x -> Re f (FMap x y)
    deriving (Typeable)

data BoolBefore = BoolBefore { before :: Bool }
type ReBBefore x = Re BoolBefore x

data BoolAfter = BoolAfter { after :: Bool }
type ReBAfter x = Re BoolAfter x

-- -- Funny enough, pass (later) works, but pass' doesn't type-check.
-- -- even though we never really look at the first argument!
-- pass' a (AltT x' y') = AltT (pass' a x') (pass' a y')
-- pass' a (CutT x' y') = CutT (pass' a x') (pass' a y')
-- pass' a (SeqT x' y') = SeqT (pass' a x') (pass' a y')

f :: Eq a => a -> Re BoolBefore x -> x -> Re BoolAfter x
f a (SymX _) (Sym (Just l)) | _ a l = SymX (BoolAfter True)
f a (AltX x' y') (Alt x y) = AltX (f a x' x) (f a y' y) -- AltX (f x x') (f y y')

-- This seems like boiler plate.
-- pass :: Eq a => x -> a -> Re BoolBefore x -> Re BoolAfter x
-- pass (Sym _) a (SymX (BoolBefore False)) = SymX (BoolAfter False)
-- pass (Sym Nothing) a (SymX (BoolBefore True)) = SymX . BoolAfter $ True
 -- SymX . BoolAfter . _ $ pass' x a x' where
{-    where
 pass' _ _ _ = False
 -- pass' _ a False = False
 -- pass' Nothing a True = True
 -- pass' (Just l) a True = a `elem` l
-}

{-
pass (Alt x y) a (AltT x' y') = AltT (pass x a x') (pass y a y')

pass (Cut x y) a (CutT x' y') = CutT (pass x a x') (pass y a y')

pass (Seq x y) a (SeqT x' y') = SeqT (pass x a x') (pass y a y')

pass (Rep x) a (RepT x') = RepT $ pass x a x'

pass (Not x) a (NotT x') = NotT $ pass x a x'

pass (Eps x) a _ = EpsT

pass Nil a _ = NilT
-}

-- pass (FMap _ x) a (FMapT x' y') = _ . FMapT  $ pass _ a _
-- 
-- epsable :: Re a x -> Bool
-- epsable (Sym _) = False
-- epsable (Alt x y) = epsable x || epsable y
-- epsable (Cut x y) = epsable x && epsable y
-- epsable (Seq x y) = epsable x && epsable y
-- epsable (Not x) = not $ epsable x
-- epsable (Rep _) = True
-- epsable (Eps _) = True
-- epsable Nil = False
-- 
-- {-
-- addFirst :: Re a x -> x -> x
-- addFirst (Sym _) (SymT _) = SymT True
-- addFirst (Alt x y) (AltT x' y') = AltT (addFirst x x') (addFirst y y')
-- addFirst (Cut x y) (CutT x' y') = CutT (addFirst x x') (addFirst y y')
-- addFirst (Seq x y) (SeqT x' y') = SeqT (addFirst x x') (if epsable x then addFirst y y' else y')
-- addFirst (Rep x) (RepT x') = RepT $ addFirst x x'
-- -- Not sure.
-- addFirst (Not x) (NotT x') = NotT $ addFirst x x'
-- addFirst (Eps _) EpsT = EpsT
-- addFirst Nil NilT = NilT
-- -}
-- 
-- -- TODO: add more types?
-- 
-- step :: Re a x -> Bool -> x -> (x, Bool)
-- step (Sym _) new (SymT old) = (SymT new, old)
-- step (Alt x y) new (AltT x' y') = let (x'', oldX) = step x new x'
--                                       (y'', oldY) = step y new y'
--                                   in (AltT x'' y'', oldX || oldY)
-- step (Seq x y) new (SeqT x' y') =
--     let (x_, newx) = step x new x'
--         (y_, newy) = step y newx y'
--     in (SeqT x_ y_, newy)
-- step (Cut x y) new (CutT x' y') = let (x'', oldX) = step x new x'
--                                       (y'', oldY) = step y new y'
--                                   in (CutT x'' y'', oldX && oldY)
-- step (Not x) new (NotT x') = NotT *** not $ step x new x'
-- -- Rep x = Eps `Alt` Seq x (Reps x)
-- -- but, avoid infinite regress..
-- step (Rep x) new (RepT x') =
--     let (x_, new_) = step x new x'
--     in (RepT x_, new || new_)
-- step (Eps _) new EpsT = (EpsT, new)
-- step Nil new NilT = (NilT, False) -- ?
-- 
