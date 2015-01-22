{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}

-- This should be sort-of like a state monad?
data Thread c x = Thread { _step :: c -> Thread c x, _n :: x }
--    Thread :: i -> Maybe [a], Thread a x 

step :: c -> Thread c x -> Thread c x
step = flip _step
-- stepn :: (Ord i, Eq c) => c -> Threads c i x -> Threads c i x
-- ?
-- step' :: (Ord i, Eq c) => c -> Thread c i x -> (i, x)

-- x will typically be a Maybe y.
n :: Thread c x -> x
n = _n

eps :: x -> x -> Thread c x
eps now forever = undefined

-- nil is the same as always.
always :: x -> Thread c x
always = undefined

nil :: Thread c (Maybe x)
nil = always Nothing

sym :: (c -> Bool) -> Thread c (Maybe c)
sym = undefined

filter' :: (c -> Bool) -> Bool -> Thread c Bool
filter' = undefined

binOp :: (x -> y -> z) -> Thread c x -> Thread c y -> Thread c z
binOp = undefined

alt :: Thread c (Maybe x) -> Thread c (Maybe y) -> Thread c (Maybe (Either x y))
alt = undefined
-- eg or/alt, and/cut
instance Functor (Thread c) where
    -- Can implement eg not.
    fmap = undefined
-- fmap' :: (x -> y) -> Thread c x -> Thread c y
-- fmap' = undefined

-- The crux of the matter!  We do need to weed out multiple similar states.
-- (Perhaps we can still leave this to the individual Threads?)
(x, y) -> (x, y) -> (x, y)
Eq (x, y)
Eq x, Eq y, Eq (x, y)
-- partial Ys, still need to know how to combine Xs
Thread c (x, y)
seq :: (x -> y -> z) -> (z -> z -> z) -> Thread c x -> Thread c y -> Thread c z
seq op by l r = Thread
    { _step = \c -> binOp by 
    , _n = op (n l) (n r)
    }

-- (length***length) <$> a* <*> a*


-- morally.
match :: Thread c x -> [c] -> x
match thread string = n $ foldl (flip step) thread string

-- matrix and flatten.
{-
type State = [x]
nil? = boolean function of state
res = [*] -> *

step :: state -> map f state -> reduce

reduce step needs IDs. (or similar)


type DFA a x = (Maybe x, a -> DFA a x)

type DFA_ a = (Bool, a -> DFA_ a)
-}
{-
seq :: dfa a x -> dfa a (x -> y) -> dfa y
app :: dfa a (x -> y) -> dfa a x -> dfa y

-- Treat this as a `free' Applicative to get labelling?
data Re a x where
    -- Ranges of letters.  Nothing stands for .
    -- TODO: Add character classes later.
    Sym :: Maybe [a] -> Re a a
    -- Alternative, |
    -- Sum
    Alt :: Re a x -> Re a y -> Re a (Either x y)
    -- Intersection
    -- (Cartesian) product
    Cut :: Re a x -> Re a y -> Re a (x,y)
    -- Sequencing
    Seq :: Re a x -> Re a y -> Re a (x,y)
    -- Repetition, Kleene Star *
    Rep :: Re a x -> Re a [x]
    -- Plus :: Re a x -> Re a (NonEmptyList x)
    -- Complement
    Not :: Re a x -> Re a ()
    -- Match empty string
    Eps :: x -> Re a x
    -- Match no string
    Nil :: Re a x
    FMap :: (x -> y) -> Re a x -> Re a y
    deriving (Typeable)

-}
