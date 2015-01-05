{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}

{-
data Thread a x where
    Thread :: (Maybe [a], Thread a x 

-- matrix and flatten.

type State = [x]
nil? = boolean function of state
res = [*] -> *

step :: state -> map f state -> reduce

reduce step needs IDs. (or similar)


type DFA a x = (Maybe x, a -> DFA a x)

type DFA_ a = (Bool, a -> DFA_ a)
-}

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


