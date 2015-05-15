{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
module Types where
import qualified Data.Set as Set
import Data.Typeable

-- Actually, we don't need any constructors for these.
-- They can exists solely on the type level.
data Sym 
    -- Is this right?
--    Sym :: Char -> Sym
    deriving (Typeable)
data Alt x y where
--    Alt2 :: x -> y -> Alt x y
--    Alt1 :: (Either x y) -> Alt x y
--    Alt :: x a -> y a -> Alt a (x a) (y a)
    deriving (Typeable)
data Cut x y where
--    Cut :: x -> y -> Cut x y
    deriving (Typeable)
data Seq x y where
--    Seq :: x -> y -> Seq x y
    deriving (Typeable)
data Not x -- where
--    Not :: x a -> Not a (x a)
    deriving (Typeable)
data Rep x where
--    Rep :: [x] -> Rep x
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
           | Uni' (Re' f) (Re' f) -- (Set.Set (Re' f))
    deriving (Typeable, Eq, Ord, Show)

-- TODO: Add Char as variable.
data SymError = BeforeSym | GotWrong | AfterSym
    deriving (Eq, Ord, Show)

data ReE f x y where
    -- Does this have to be in here?
    UniE :: Set.Set (ReE f x y) -> ReE f x y
    -- Or perhaps different?
    SymE :: f -> ReE f Sym SymError
    -- De Morgan
    AltE :: ReE f x y -> ReE f x' y' -> ReE f (Alt x x') (Cut y y')
    CutE :: ReE f x y -> ReE f x' y' -> ReE f (Cut x x') (Alt y y')
    -- Is that error type right?
    -- (Alternative was just Alt y y'
    SeqE :: ReE f x y -> ReE f x' y' -> ReE f (Seq x x') (Either y (Seq x y'))
    -- Is that error type right?
    RepE :: ReE f x y               -> ReE f (Rep x) (Seq (Rep x) y)
    -- RepEM :: ReE f x y -> ReE f x y -> ReE f (Rep x) (Seq (Rep x) y)
    -- No explicit Not required?
    NotE :: ReE f x y -> ReE f y x
    -- NotE :: ReE f x y -> ReE f (Not y) (Not x)
    -- Not quite sure if we don't need a wrapper or so?
    EpsE :: ReE f () ()
    NilE :: ReE f () ()
    -- This is giving me trouble when comparing..
    FMapE :: (x -> x') -> (y -> y') -> ReE f x y -> ReE f x' y'

instance (Eq f) => Eq (ReE f x y) where
    (UniE set) == (UniE set') = set == set'
    (SymE x) == (SymE x') = x == x'
    (AltE x y) == (AltE x' y') = (x,y) == (x',y')
    (CutE x y) == (CutE x' y') = (x,y) == (x',y')
    (SeqE x y) == (SeqE x' y') = (x,y) == (x',y')
    (RepE x) == (RepE x') = x == x'
    (NotE x) == (NotE x') = x == x'
    EpsE == EpsE = True
    NilE == NilE = True
    -- Only comparable if they have the same structure?
    -- Or switch to Re'?
    -- (FMapE _ _ x) == (FMapE _ _ x') = x == x'
    _ == _ = False
instance (Ord f) => Ord (ReE f x y) where

type Range = Maybe [Char]

class RE r where
    sym :: Range -> r
    alt :: r -> r -> r
    seq :: r -> r -> r
    rep :: r -> r

-- back in Char for now.  TODO: make flexible.
data ReRes x where
    SymErr :: SymError -> ReRes SymError
    SymRes :: Char -> ReRes Sym
--    Alt1 :: Either (ReRes x) (ReRes y) -> ReRes (Alt x y)
--    Alt2 :: ReRes x -> ReRes y -> ReRes (Alt x y)

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

-- focus on one alt-strand.
data ReS1 x where
    Before :: ReS1 x
    -- SymS :: ReS1 Sym
    AltSL :: ReS1 x -> ReS1 (Alt x y)
    AltSR :: ReS1 y -> ReS1 (Alt x y)
    CutS :: ReS1 x -> ReS1 y -> ReS1 (Cut x y)
    -- magic here!
    SeqSL :: ReS1 x -> ReS1 (Seq x y)
    SeqSR :: ReS1 y -> ReS1 (Seq x y)
    RepS :: ReS1 x -> ReS1 (Rep x)
    -- bah, need cut, too, instead of just alt..
    NotS :: ReC x -> ReS1 (Not x)
    -- or ReS1 x?
    EpsS :: x -> ReS1 x
    NilS :: ReS1 x


-- one cut-strain, under NOT
data ReC x where
    SymC :: ReC Sym
    AltC :: ReC x -> ReC y -> ReC (Alt x y)
    CutC1 :: ReC x -> ReC (Cut x y)
    CutC2 :: ReC y -> ReC (Cut x y)
    -- magic here!
    SeqCL :: ReC x -> ReC (Seq x y)
    SeqCR :: ReC y -> ReC (Seq x y)
    RepC :: ReC x -> ReC (Rep x)
    -- change to alt..
    NotC :: ReS1 x -> ReC (Not x)
    -- or ReS1 x?
    EpsC :: x -> ReC x
    NilC :: ReC x
    

data BoolBefore = BoolBefore { before :: Bool }
type ReBBefore x = Re BoolBefore x

data BoolAfter = BoolAfter { after :: Bool }
type ReBAfter x = Re BoolAfter x
