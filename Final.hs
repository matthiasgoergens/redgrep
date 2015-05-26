{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
module Final where
import GHC.Generics hiding (R)
import Data.Bifunctor
import Control.Applicative
import Control.Monad
import Prelude hiding (seq, not)
import qualified Prelude as P
import qualified Types as T
import Util
import Data.List
import Data.String
import Data.Ord
import Control.Arrow ((***), (&&&))

{-
Progress here:
    - composability solves expression problem.  Since our reg-ex language has quite a few elements,
    this makes exploratory implementation easier!
    - (Bi)Functor instance was no problem at all.  (I think I only had problems with this at first,
    when I didn't really know how to use GADTs and phantom types properly in the `Initial' version.
        + Some of the more interesting interpreters have interesting Bifunctor instances.
    - Applicative's pure gives me problem because of my non-uni / multi error type.
    - We'd need a bi-functor.  Bi-applicative doesn't work for the same reason that applicative doesn't work.
-}

-- Before needs to be last, to make merging with max work.
data SymE = TooMany | Wrong Range Char | Before
    deriving (Eq, Ord, Show, Generic)
data AltI a b = AltL a | AltR b
    deriving (Eq, Ord, Show, Functor, Generic)
instance Bifunctor AltI where
    bimap f _ (AltL a) = AltL $ f a
    bimap _ g (AltR b) = AltR $ g b
data CutI a b = Cut a b
    deriving (Eq, Ord, Show, Functor, Generic)
instance Bifunctor CutI where
    bimap f g (Cut a b) = Cut (f a) (g b)
data SeqI a b = Seq a b
    deriving (Eq, Ord, Show, Functor, Generic)
instance Bifunctor SeqI where
    bimap f g (Seq a b) = Seq (f a) (g b)
data RepI a = Rep [a]
    deriving (Eq, Ord, Show, Functor, Generic)

type Range = Maybe [Char]

-- r = representation
-- f = failure
-- s = success

class (Bifunctor r) => RE r where
    sym :: Range -> r SymE Char
    alt :: r f s -> r f' s' -> r (CutI f f') (AltI s s')
    cut :: r f s -> r f' s' -> r (AltI f f') (CutI s s')
    seq :: r f s -> r f' s' -> r (AltI f (SeqI s f')) (SeqI s s') 
    rep :: r f s -> r (SeqI (RepI s) f) (RepI s)
    not :: r s f -> r f s
    eps :: f -> s -> r f s
    nil :: f -> r f s

eps_ = eps () ()
nil_ = nil ()

data REini f s where
    SymX :: Range -> REini SymE Char
    AltX :: REini f s -> REini f' s' -> REini (CutI f f') (AltI s s')
    CutX :: REini f s -> REini f' s' -> REini (AltI f f') (CutI s s')
    SeqX :: REini f s -> REini f' s' -> REini (AltI f (SeqI s f')) (SeqI s s') 
    RepX :: REini f s -> REini (SeqI (RepI s) f) (RepI s)
    NotX :: REini s f -> REini f s
    EpsX :: f -> s -> REini f s
    NilX :: f -> REini f s
    
    Bimap :: (f' -> f) -> (s' -> s) -> REini f' s' -> REini f s

instance Show (REini f s) where
    show = show . rf . forget . run

instance Functor (REini f) where
    fmap = Bimap id
instance Bifunctor REini where
    bimap = Bimap
instance RE REini where
    sym = SymX
    alt = AltX
    cut = CutX
    seq = SeqX
    rep = RepX
    not = NotX
    eps = EpsX
    nil = NilX

run :: (Bifunctor r, RE r) => REini f s -> r f s
run (SymX r)      = sym r
run (AltX x y)    = alt (run x) (run y)
run (CutX x y)    = cut (run x) (run y)
run (SeqX x y)    = seq (run x) (run y)
run (RepX x)      = rep (run x)
run (NotX x)      = not (run x)
run (EpsX f s)    = eps f s
run (NilX f)      = nil f
run (Bimap f s x) = bimap f s (run x)





data Both x y f s = Both { one :: (x f s), two :: (y f s) }
unBoth = (one &&& two)
both = uncurry Both

instance (RE l, RE r) => RE (Both l r) where
    sym range = Both (sym range) (sym range)
    alt (Both l l') (Both r r') = Both (alt l r) (alt l' r')
    cut (Both l l') (Both r r') = Both (cut l r) (cut l' r')
    seq (Both l l') (Both r r') = Both (seq l r) (seq l' r')
    rep (Both x y) = Both (rep x) (rep y)
    not (Both x y) = Both (not x) (not y)
    eps f s = Both (eps f s) (eps f s)
    nil f = Both (nil f) (nil f)

instance (Functor (l f), Functor (r f)) => Functor (Both l r f) where
    fmap fn (Both l r) = Both (fmap fn l) (fmap fn r)
instance (Bifunctor l, Bifunctor r) =>  Bifunctor (Both l r) where
    bimap h g (Both l r) = Both (bimap h g l) (bimap h g r)

newtype Phantom a f s = Phantom { forget :: a }
    deriving (Generic, Eq, Ord, Show)
p = Phantom

wrapPhantom op x y = Phantom $ op (forget x) (forget y)

type R = T.Re' T.Range
instance RE (Phantom R) where
    sym = p . T.Sym'
    alt = wrapPhantom T.Alt'
    cut = wrapPhantom T.Cut'
    seq = wrapPhantom T.Seq'
    rep = p . T.Rep' . forget
    not = p . T.Not' . forget
    eps _ _ = p T.Eps'
    nil _ = p T.Nil'
instance Functor (Phantom R f) where fmap _ (Phantom x) = Phantom x
instance Bifunctor (Phantom R) where bimap _ _ (Phantom x) = Phantom x

data Re'f f = Sym' f | Alt' (Re'f f) (Re'f f) | Cut' (Re'f f) (Re'f f)
           | Seq' (Re'f f) (Re'f f) | Rep' (Re'f f) | Not' (Re'f f)
           | Eps' | Nil'
           | Uni' (Re'f f) (Re'f f) -- (Set.Set (Re'f f))
           | Bimap' (Re'f f)
    deriving (Eq, Ord, Show)

rf :: Rf -> Rf
rf = id
type Rf = Re'f T.Range
instance RE (Phantom Rf) where
    sym = p . Sym'
    alt = wrapPhantom Alt'
    cut = wrapPhantom Cut'
    seq = wrapPhantom Seq'
    rep = p . Rep' . forget
    not = p . Not' . forget
    eps _ _ = p Eps'
    nil _ = p Nil'
instance Functor (Phantom Rf f) where fmap _ (Phantom x) = Phantom (Bimap' x)
instance Bifunctor (Phantom Rf) where bimap _ _ (Phantom x) = Phantom (Bimap' x)

string :: (RE r) => String -> r () String
string s = foldr h (eps () []) s where
    h char r = bimap fail succ $ seq (c char) r
    succ (Seq c r) = c : r
    -- TODO: figure out good error reporting
    fail (AltL l) = ()
    fail (AltR r) = ()

-- or last Left
firstRight :: Either a b -> [Either a b] -> Either a b
firstRight a l = foldr1 (+++) (a : l) where

r@(Right _) +++ _ = r
_ +++ b = b

cutD x y = not $ alt (not x) (not y)
switch :: Either a b -> Either b a
switch (Left a) = Right a
switch (Right b) = Left b

c :: RE r => Char -> r SymE Char
c x = sym . pure . pure $ x
xh :: RE r => r SymE Char
xh = sym (Just "xh")

hello :: RE r => r (AltI SymE (SeqI Char SymE)) (SeqI Char Char)
hello = c 'h' `seq` c 'e'

hello2 :: RE r => r (AltI Char (SeqI SymE SymE)) (SeqI SymE Char)
hello2 = not (c 'h') `seq` c 'e'

hello3 :: RE r =>
    r (AltI SymE (SeqI Char (SeqI (RepI Char) SymE)))
      (SeqI Char (RepI Char))
hello3 = (c 'h') `seq` rep (c 'e')


-- optional :: (Alt r, Eps r) => r (AltI () Char) (CutI 

r b = putStr "R " >> b
l b = putStr "L " >> b

xTest = rep "hello world "

main = do
    return ()
{-
    print $ evalB (sym (Just "xh")) "xhello"
    print $ evalB hello "he"
    print $ evalB hello "xx"
    print $ evalB hello2 "xe"
    print $ evalB hello3 "heeex"
    print $ evalB hello3 "heeee"
    r $ print $ evalB (sym Nothing) "a"
    r $ print $ evalB (rep (sym Nothing)) "aaaa"
    r $ print $ evalB (eps 12 () `alt` c 'x') ""
    let s = string
    r $ print $ evalB (seq ((s "a" `seq` rep (s "ba")) `cut`
                           (rep (s "ab") `seq` (s "a")))
                        $ c 'x')
                    "ababax"
    r $ print $ evalB (seq ((s "a" `seq` rep (s "ba")) `cutD`
                           (rep (s "ab") `seq` (s "a")))
                        $ c 'x')
                    "ababax"
-}
