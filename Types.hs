{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, OverlappingInstances #-}
module Types where
import Data.Typeable

data Sym
--    Sym :: Maybe [a] -> Sym a
    deriving (Typeable)
data Alt x y
--    Alt :: x a -> y a -> Alt a (x a) (y a)
    deriving (Typeable)
data Cut x y -- where
--     Cut :: x a -> y a -> Cut a (x a) (y a)
    deriving (Typeable)
data Seq x y -- where
--    Seq :: x a -> y a -> Seq a (x a) (y a)
    deriving (Typeable)
data Not x -- where
--    Not :: x a -> Not a (x a)
    deriving (Typeable)
data Rep x -- where
--    Rep :: x a -> Rep a (x a)
    deriving (Typeable)
-- Do we need `a' for Eps?
data Eps x -- where
--    Eps :: x -> Eps x
    deriving (Typeable)
data Nil -- where
--    Nil :: Nil
    deriving (Typeable)

data FMap a x y -- where
--    FMap :: (x a -> y a) -> x a -> FMap a (x a) (y a)
    deriving (Typeable)

-- Less types, for easier generation.
data Re' f = Sym' f | Alt' (Re' f) (Re' f) | Cut' (Re' f) (Re' f)
           | Seq' (Re' f) (Re' f) | Rep' (Re' f) | Not' (Re' f)
           | Eps' | Nil'
    deriving (Typeable, Eq, Ord, Show)

data ReE f x y where
    -- Or perhaps different?
    SymE :: f -> ReE f Sym Sym
    -- De Morgan
    AltE :: ReE f x y -> ReE f x' y' -> ReE f (Alt x x') (Cut y y')
    CutE :: ReE f x y -> ReE f x' y' -> ReE f (Cut x x') (Alt y y')
    -- Is that error type right?
    -- (Alternative was just Alt y y'
    SeqE :: ReE f x y -> ReE f x' y' -> ReE f (Seq x x') (Alt y (Seq x y'))
    -- Is that error type right?
    RepE :: ReE f x y -> ReE f (Rep x) (Seq (Rep x) y)
    -- No explicit Not required?
    NotE :: ReE f x y -> ReE f y x
    -- NotE :: ReE f x y -> ReE f (Not y) (Not x)
    EpsE :: x -> ReE f x y
    NilE :: y -> ReE f x y
    FMapE :: (x -> x') -> (y -> y') -> ReE f x y -> ReE f x' y'



data Re f x where
    -- Ranges of letters.  Nothing stands for .
    -- TODO: Add character classes later.
    SymX :: f -> Re f Sym
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
    -- Note: Type doubtful.  (Since we are trying to unify the spec and the state
    -- of our machine here.
    EpsX :: x -> Re f (Eps x)
    -- Match no string
    NilX :: Re f Nil
    -- -- Do we need something like the lens trick?
    -- This might not work!
    -- Value-bearing will make this more complicated.
    -- FMapX :: x -> y -> Re f x -> Re f (FMap x y)
    deriving (Typeable)

data BoolBefore = BoolBefore { before :: Bool }
type ReBBefore x = Re BoolBefore x

data BoolAfter = BoolAfter { after :: Bool }
type ReBAfter x = Re BoolAfter x