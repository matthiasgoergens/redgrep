-- Proof of concept for fmap floating up in the final setting.
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

import Control.Arrow

class Add1 r where
    p1 :: r Int -> r Int
    add1 :: r x -> r (Int,x)
    l :: Int -> r Int

instance Add1 Maybe where
    p1 = fmap (1+)
    add1 = fmap (1,)
    l = pure

newtype Zahl a = Z a
    deriving (Eq, Ord, Show)
instance Add1 Zahl where
    p1 (Z a) = Z $ (a + 1)
    add1 (Z a) = Z $ (1,a)
    l = Z
instance Functor Zahl where
    fmap f (Z a) = Z $ f a

newtype Pretty a = P String
    deriving (Eq, Ord, Show)
instance Add1 Pretty where
    p1 (P a) = P $ "(1 + " ++ a ++ ")"
    add1 (P a) = P $ "(1, " ++ a ++ ")"
    l = P . show
instance Functor Pretty where
    fmap fn (P a) = P $ "FMap " ++ a

data Both a b x = Both (a x) (b x)
    deriving (Eq, Ord, Show)
instance (Add1 a, Add1 b) => Add1 (Both a b) where
    p1 (Both a b) = Both (p1 a) (p1 b)
    add1 (Both a b) = Both (add1 a) (add1 b)
    l x = Both (l x) (l x)
instance (Functor a, Functor b) => Functor (Both a b) where
    fmap fn (Both a b) = Both (fmap fn a) (fmap fn b)

s (P s) = s
c :: Maybe x -> Maybe x
c = id
z (Z x) = x

out :: Both a b x -> (a x, b x)
out (Both a b) = (a, b)

two :: Both a b x -> b x
two (Both a b) = b

data NF r b = ID (r b) | forall a . NF (a -> b) (r a)

instance (Functor r, Add1 r) => Add1 (NF r) where
    p1 (ID r) = ID $ p1 r
    p1 (NF fn r) = NF id (p1 $ fmap fn r)
    add1 (ID r) = ID $ add1 r
    add1 (NF fn r) = NF id (add1 $ fmap fn r)
    l i = ID $ l i
    l i = NF id $ l i
instance (Functor r) => Functor (NF r) where
    fmap fn (ID r) = NF fn r
    fmap fn (NF fn' r) = NF (fn . fn') r

nf :: Functor r => NF r b -> r b
nf (ID r) = r
nf (NF f r) = fmap f r


type Either' a b = forall c . ((a -> c) -> (b -> c) -> c) -> c
type Tuple a b = forall c . (a -> b -> c) -> c

-- data Ctx r b = FMap (forall a . ((b -> a) -> r a) (r b)

type IDContext r b a = (r b -> r a)
type FMapContext r b a c = ((c -> b) -> r c -> r a)

-- fmap' :: (b -> b') -> (FMapContext r b a c -> a) -> (FMapContext r b' a c -> a)


data NF' r b = forall a. NF' (r b, ((a -> b), r a))
-- data NF'' r b --  ...

conv :: Functor r => NF r b -> NF' r b
conv (NF f b) = NF' (fmap f b, (f, b))
conv (ID b) = NF' (b, (id, b))

((a -> b -> c) -> c) -> c
((a -> c) -> (b -> c) -> c)

x = add1 . p1 . fmap fst . fmap (fmap (++" world")) . fmap (,"hello") . p1 $ l 10
y = l 10

main = do
    print $ s x
--     print $ c x
--    print $ z x
--    print $ s *** c $ out $ x
    print $ s $ nf $ x
    print $ z $ nf $ x
    print $ s $ nf y
