{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}

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
import Data.Bifunctor.Apply
-- import Control.Lens hiding (elements)
-- import Control.Lens.Prism

data Alt_ x y where
    Alt_ :: x -> y -> Alt_ x y
    deriving (Typeable)

-- newtype N a = N { n :: Maybe [a] } deriving (Typeable, Eq, Ord, Show, Functor)
type N a = Maybe [a]

xxx :: Re (N a) (Alt Sym Sym)
xxx = AltX (SymX Nothing) (SymX Nothing)

yyy :: Re BoolBefore (Alt x Sym)
yyy = AltX undefined zzz

zzz :: Re BoolBefore Sym
zzz = SymX (BoolBefore True)

-- -- This don't work.  Silly!  It's just a shuffling of the arguments..
-- h :: Eq a => x a -> a -> Re a BoolBefore (x a) -> Re a BoolAfter (x a)
-- h (Sym l) a (SymX (BoolBefore before)) = SymX (BoolAfter $ before && maybe True (elem a) l)

-- g :: Eq a => x a -> a -> Re a BoolBefore (x c) -> Re a BoolAfter (x c)
-- g re a rex = f a re rex

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

data Re' f = Sym' f | Alt' (Re' f) (Re' f) | Cut' (Re' f) (Re' f)
           | Seq' (Re' f) (Re' f) | Rep' (Re' f) | Not' (Re' f)
           | Eps' | Nil'
    deriving (Typeable, Eq, Ord, Show)

instance Show (Re (Maybe [Char]) x) where
    showsPrec d re = case re of
        SymX Nothing -> showString "."
        SymX (Just [x]) -> showsPrec d x
        SymX (Just xs) -> showString ("[" ++ init (tail $ show xs) ++ "]")
        AltX a b -> showParen (d > 5) $ showsPrec 6 a . showString "|" . showsPrec 6 b
        CutX a b -> showParen (d > 6) $ showsPrec 7 a . showString "&" . showsPrec 7 b
        SeqX a b -> showParen (d > 9) $ showsPrec 10 a . showsPrec 10 b
        RepX a -> showParen (d > 10) $ showsPrec 11 a . showString "*"
        NotX (EpsX _) -> showParen (d > 8) $ showString ".+"
        NotX NilX -> showParen (d > 8) $ showString ".*"
        NotX a -> showParen (d > 8) $ showString "!" . showsPrec 9 a
        EpsX _ -> showString "ε"
        NilX -> showString "∅"
--        FMap _ a -> showParen (d > 8) $ showString "$" . showsPrec 9 a -- Not great.

instance Show (Re BoolAfter x) where
    showsPrec d re = case re of
        SymX (BoolAfter True) -> showString "+"
        SymX (BoolAfter False) -> showString "-"
        AltX a b -> showParen (d > 5) $ showsPrec 6 a . showString "|" . showsPrec 6 b
        CutX a b -> showParen (d > 6) $ showsPrec 7 a . showString "&" . showsPrec 7 b
        SeqX a b -> showParen (d > 9) $ showsPrec 10 a . showsPrec 10 b
        RepX a -> showParen (d > 10) $ showsPrec 11 a . showString "*"
        NotX (EpsX _) -> showParen (d > 8) $ showString ".+"
        NotX NilX -> showParen (d > 8) $ showString ".*"
        NotX a -> showParen (d > 8) $ showString "!" . showsPrec 9 a
        EpsX _ -> showString "ε"
        NilX -> showString "∅"

instance Show (Re BoolBefore x) where
    showsPrec d re = case re of
        SymX (BoolBefore True) -> showString "+"
        SymX (BoolBefore False) -> showString "-"
        AltX a b -> showParen (d > 5) $ showsPrec 6 a . showString "|" . showsPrec 6 b
        CutX a b -> showParen (d > 6) $ showsPrec 7 a . showString "&" . showsPrec 7 b
        SeqX a b -> showParen (d > 9) $ showsPrec 10 a . showsPrec 10 b
        RepX a -> showParen (d > 10) $ showsPrec 11 a . showString "*"
        NotX (EpsX _) -> showParen (d > 8) $ showString ".+"
        NotX NilX -> showParen (d > 8) $ showString ".*"
        NotX a -> showParen (d > 8) $ showString "!" . showsPrec 9 a
        EpsX _ -> showString "ε"
        NilX -> showString "∅"


{-
conv :: Re f x -> Re' f
conv (SymX f) = Sym' f
conv (AltX x y) = Alt' (conv x) (conv y)
conv (CutX x y) = Cut' (conv x) (conv y)
conv (SeqX x y) = Seq' (conv x) (conv y)
conv
-}


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

-- Bi-functor?  Something like it..
-- newtype Ref x f = Ref { unRef :: Re f x }
-- instance Functor (Ref x) where
--    fmap f (Ref r) = Ref $ h r

h :: (f -> g) -> Re f x -> Re g x
h f (SymX l) = SymX $ f l
h f (AltX x y) = AltX (h f x) (h f y)
h f (CutX x y) = CutX (h f x) (h f y)
h f (SeqX x y) = SeqX (h f x) (h f y)
h f (NotX x) = NotX (h f x)
h f (RepX x) = RepX (h f x)
h f (EpsX x) = EpsX x
h f NilX = NilX

-- -- Funny enough, pass (later) works, but pass' doesn't type-check.
-- -- even though we never really look at the first argument!
-- pass' a (AltT x' y') = AltT (pass' a x') (pass' a y')
-- pass' a (CutT x' y') = CutT (pass' a x') (pass' a y')
-- pass' a (SeqT x' y') = SeqT (pass' a x') (pass' a y')

-- There's lots of boiler plate here.

-- Can go from (x a) to (x c) for some, for more general type.
pass :: Eq a => a -> Re BoolBefore x -> Re (Maybe [a]) x -> Re BoolAfter x
pass a (SymX (BoolBefore before)) (SymX l) = SymX . BoolAfter $ before && maybe True (elem a) l

pass a (AltX x y) (AltX x' y') = AltX (pass a x x') (pass a y y')
pass a (CutX x y) (CutX x' y') = CutX (pass a x x') (pass a y y')
pass a (SeqX x y) (SeqX x' y') = SeqX (pass a x x') (pass a y y')

pass a (RepX x) (RepX x') = RepX $ pass a x x'
pass a (NotX x) (NotX x') = NotX $ pass a x x'

-- Or should this be NilX?
pass a (EpsX x) _ = (EpsX x)

pass a NilX NilX = NilX

-- pass (FMap _ x) a (FMapT x' y') = _ . FMapT  $ pass _ a _

epsable :: Re f x -> Bool
epsable (SymX _) = False
epsable (AltX x y) = epsable x || epsable y
epsable (CutX x y) = epsable x && epsable y
epsable (SeqX x y) = epsable x && epsable y
epsable (NotX x) = not $ epsable x
epsable (RepX _) = True
epsable (EpsX _) = True
epsable NilX = False
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
step :: Bool -> Re BoolAfter x -> (Bool, Re BoolBefore x)
step new (SymX (BoolAfter old)) = (old, SymX (BoolBefore new))
step new (AltX x y) = ((||), AltX) <<.>> step new x <<.>> step new y
step new (SeqX x y) =
    let (newx, x') = step new x
        (newy, y') = step newx y
    -- Nice and typesafe: Try mixing up x' and x!
    in (newy, SeqX x' y')
step new (CutX x y) = ((&&), CutX) <<.>> step new x <<.>> step new y
step new (NotX x) = not *** NotX $ step new x
-- Avoid infinite regress, but get this right..
-- Tricky!  Let's hope this is the right approach!
step new (RepX x) =
    -- suss out existing!
    let (old_, _) = step False x
        (old, x') = step (new || old_) x
    in (new || old, RepX x')
step new (EpsX x) = (new, EpsX x)
step new NilX = (False, NilX) -- ?

make :: Re f x -> Re BoolAfter x
make = h (const $ BoolAfter False)

-- step :: Bool -> Re BoolAfter x -> (Bool, Re BoolBefore x)
-- pass :: Eq a => a -> Re BoolBefore x -> Re (Maybe [a]) x -> Re BoolAfter x
match1 :: Eq a => Re (Maybe [a]) x -> a -> Bool -> Re BoolAfter x -> Re BoolAfter x
match1 re a start state =
    let (_, bbefore) = step start state
    in pass a bbefore re

match :: Eq a => Re (N a) x -> [a] -> Bool
match re s = fst $ step False $ foldl (.) id (zipWith (match1 re) s (True : repeat False)) (make re)


test = match (EpsX "bla") "1"
