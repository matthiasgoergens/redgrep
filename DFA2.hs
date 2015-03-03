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

-- -- Dense representation.
-- We actually don't need the contrustors, or do we?
data Sym a where
    SymT :: Bool -> Sym Bool
    deriving (Typeable)
data Alt x y where
    AltT :: x -> y -> Alt x y
    deriving (Typeable)
data Cut x y where
     CutT :: x -> y -> Cut x y
    deriving (Typeable)
data Seq x y where
    SeqT :: x -> y -> Seq x y
    deriving (Typeable)
data Not x where
    NotT :: x -> Not x
    deriving (Typeable)
data Rep x where
    RepT :: x -> Rep x
    deriving (Typeable)
data Eps x = EpsT
    deriving (Typeable)
data Nil x = NilT
    deriving (Typeable)

{-
-- -- Sparse representation.
-- We actually don't need the contrustors, or do we?
data Sym a = SymT Bool
    deriving (Typeable)
data Alt x y = AltT (Maybe x) (Maybe y)
    deriving (Typeable)
data Cut x y = CutT (Maybe x) (Maybe y)
    deriving (Typeable)
data Seq x y = SeqT (Maybe x) (Maybe y)
    deriving (Typeable)
data Not x = NotT (Maybe x)
    deriving (Typeable)
data Rep x = RepT (Maybe x)
    deriving (Typeable)
data Eps x = EpsT
    deriving (Typeable)
data Nil x = NilT
    deriving (Typeable)
-}

-- data FMap x y = FMapT (x -> y) y

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
    -- -- Do we need something like the lens trick?
    -- FMap :: (x -> y) -> Re a x -> Re a (FMap x y)
    deriving (Typeable)

-- This seems like boiler plate.
pass :: Ord a => Re a x -> a -> x -> x
pass (Sym x) a (SymT x') = SymT $ (pass' x a) x' where
 pass' _ a False = False
 pass' Nothing a True = True
 pass' (Just l) a True = a `elem` l

pass (Alt x y) a (AltT x' y') = AltT (pass x a x') (pass y a y')

pass (Cut x y) a (CutT x' y') = CutT (pass x a x') (pass y a y')

pass (Seq x y) a (SeqT x' y') = SeqT (pass x a x') (pass y a y')

pass (Rep x) a (RepT x') = RepT $ pass x a x'

pass (Not x) a (NotT x') = NotT $ pass x a x'

pass (Eps x) a _ = EpsT

pass Nil a _ = NilT

-- pass (FMap _ x) a (FMapT x' y') = _ . FMapT  $ pass _ a _

epsable :: Re a x -> Bool
epsable (Sym _) = False
epsable (Alt x y) = epsable x || epsable y
epsable (Cut x y) = epsable x && epsable y
epsable (Seq x y) = epsable x && epsable y
epsable (Not x) = not $ epsable x
epsable (Rep _) = True
epsable (Eps _) = True
epsable Nil = False

{-
addFirst :: Re a x -> x -> x
addFirst (Sym _) (SymT _) = SymT True
addFirst (Alt x y) (AltT x' y') = AltT (addFirst x x') (addFirst y y')
addFirst (Cut x y) (CutT x' y') = CutT (addFirst x x') (addFirst y y')
addFirst (Seq x y) (SeqT x' y') = SeqT (addFirst x x') (if epsable x then addFirst y y' else y')
addFirst (Rep x) (RepT x') = RepT $ addFirst x x'
-- Not sure.
addFirst (Not x) (NotT x') = NotT $ addFirst x x'
addFirst (Eps _) EpsT = EpsT
addFirst Nil NilT = NilT
-}

-- TODO: add more types?

step :: Re a x -> Bool -> x -> (x, Bool)
step (Sym _) new (SymT old) = (SymT new, old)
step (Alt x y) new (AltT x' y') = let (x'', oldX) = step x new x'
                                      (y'', oldY) = step y new y'
                                  in (AltT x'' y'', oldX || oldY)
step (Seq x y) new (SeqT x' y') =
    let (x_, newx) = step x new x'
        (y_, newy) = step y newx y'
    in (SeqT x_ y_, newy)
step (Cut x y) new (CutT x' y') = let (x'', oldX) = step x new x'
                                      (y'', oldY) = step y new y'
                                  in (CutT x'' y'', oldX && oldY)
step (Not x) new (NotT x') = NotT *** not $ step x new x'
-- Rep x = Eps `Alt` Seq x (Reps x)
-- but, avoid infinite regress..
step (Rep x) new (RepT x') =
    let (x_, new_) = step x new x'
    in (RepT x_, new || new_)
step (Eps _) new EpsT = (EpsT, new)
step Nil new NilT = (NilT, False) -- ?

