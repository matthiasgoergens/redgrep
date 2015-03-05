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

data Alt_ a x y where
    Alt_ :: x a -> y a -> Alt_ a (x a) (y a)
    deriving (Typeable)

-- xxx :: Alt_ Char (Sym Char) (Sym Char)
xxx = Alt_ (Sym Nothing) (Sym Nothing)
yyy :: Req Char BoolBefore (Alt_ Char x (Sym Char))
yyy = AltQ undefined zzz

zzz :: Req Char BoolBefore (Sym Char)
zzz = SymQ (BoolBefore True)

data Req a f x where
    -- Ranges of letters.  Nothing stands for .
    -- TODO: Add character classes later.
    SymQ :: f a -> Req a f (Sym a)
    -- Alternative, |
    AltQ :: Req a f x -> Req a f y -> Req a f (Alt_ a x y)

f :: Eq a => a -> Re a BoolBefore (x c) -> x a -> Re a BoolAfter (x c)
f a (SymX (BoolBefore True)) (Sym (Just l)) | elem a l = SymX (BoolAfter True)
-- f a (AltQ x' y') (Alt_ x y) = undefined -- AltQ (f a x' x) (f a y' y) -- AltX (f x x') (f y y')


data Sym a where
    Sym :: Maybe [a] -> Sym a
    deriving (Typeable)
data Alt a x y where
    Alt :: x a -> y a -> Alt a (x a) (y a)
    deriving (Typeable)
data Cut a x y where
     Cut :: x a -> y a -> Cut a (x a) (y a)
    deriving (Typeable)
data Seq a x y where
    Seq :: x a -> y a -> Seq a (x a) (y a)
    deriving (Typeable)
data Not a x where
    Not :: x a -> Not a (x a)
    deriving (Typeable)
data Rep a x where
    Rep :: x a -> Rep a (x a)
    deriving (Typeable)
-- Do we need `a' for Eps?
data Eps x where
    Eps :: x -> Eps x
    deriving (Typeable)
data Nil where
    Nil :: Nil
    deriving (Typeable)

data FMap a x y where
    FMap :: (x a -> y a) -> x a -> FMap a (x a -> y a) (x a)
    deriving (Typeable)

data Re a f x where
    -- Ranges of letters.  Nothing stands for .
    -- TODO: Add character classes later.
    SymX :: f a -> Re a f (Sym a)
    -- Alternative, |
    AltX :: Re a f x -> Re a f y -> Re a f (Alt a x y)
    -- Intersection
    CutX :: Re a f x -> Re a f y -> Re a f (Cut a x y)
    -- Sequencing
    SeqX :: Re a f x -> Re a f y -> Re a f (Seq a x y)
    -- Repetition, Kleene Star *
    RepX :: Re a f x -> Re a f (Rep a x)
    -- Plus :: Re x -> Re (NonEmptyList x)
    -- Complement
    NotX :: Re a f x -> Re a f (Not a x)
    -- Match empty string
    EpsX :: x -> Re a f (Eps x)
    -- Match no string
    NilX :: Re a f Nil 
    -- -- Do we need something like the lens trick?
    -- This might not work!
    -- FMapX :: (x a -> y a) -> Re a f (x a) -> Re a f (FMap a x y)
    deriving (Typeable)

data BoolBefore a = BoolBefore { before :: Bool }
type ReBBefore a x = Re a BoolBefore x

data BoolAfter a = BoolAfter { after :: Bool }
type ReBAfter a x = Re a BoolAfter x

-- -- Funny enough, pass (later) works, but pass' doesn't type-check.
-- -- even though we never really look at the first argument!
-- pass' a (AltT x' y') = AltT (pass' a x') (pass' a y')
-- pass' a (CutT x' y') = CutT (pass' a x') (pass' a y')
-- pass' a (SeqT x' y') = SeqT (pass' a x') (pass' a y')

-- f :: Eq a => a -> Req a BoolBefore (x a) -> x a -> Req a BoolAfter (x a)
-- -- f a (SymX _) (Sym (Just l)) | _ a l = SymX (BoolAfter True)
-- f a (AltQ x' y') (Alt_ x y) = AltQ (f a x' x) (f a y' y) -- AltX (f x x') (f y y')

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
