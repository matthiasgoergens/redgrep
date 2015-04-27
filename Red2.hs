{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, OverlappingInstances #-}

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

import Types

-- import Control.Lens hiding (elements)
-- import Control.Lens.Prism 



-- This is the heart of the derivative based algorithm.
-- Everything else just needs to support these operations

type SymResult = Maybe (Either Char SymError)

extract :: ReE SymResult x y -> Maybe (Either (a x) (a y))
extract = undefined

v' :: ReE f x y -> Either y x
v' (SymE _) = Left BeforeSym
v' (AltE a b) = case (v' a, v' b) of
    (Right a, Right b) -> Right $ Alt2 a b
    (Right a, Left _) -> Right $ Alt1 (Left a)
    (Left _, Right b) -> Right $ Alt1 (Right b)
    (Left a, Left b) ->  Left $ Cut a b
v' (CutE a b) = case (v' a, v' b) of
    (Right a, Right b) -> Right $ Cut a b
    (Right a, Left b) -> Left $ Alt1 (Right b)
    (Left a, Right b) -> Left $ Alt1 (Left a)
    (Left a, Left b) ->  Left $ Alt2 a b
v' (SeqE a b) = case (v' a, v' b) of
    (Right a, Right b) -> Right $ Seq a b
    (Right a, Left b) -> Left $ Right (Seq a b)
    (Left a, _) -> Left $ Left a
v' (RepE a) = Right $ Rep []
v' (RepEM a b) = case v' a of
    Left a -> Left (Seq (Rep []) a)
    Right b -> Right $ Rep [b]
v' (NotE a) = case v' a of
    Left a -> Right a
    Right b -> Left b
v' (EpsE x) = Right x
v' (NilE y) = Left y

v :: ReE f x y -> ReE f x y
v = either NilE EpsE . v'

type Range = Maybe [Char]

-- Need to add things coming in.
-- trans :: Char -> ReE SymResult x y -> ReE Range x y -> ReE SymResult x y
-- trans c (SymE res) (SymE range) = SymE $ case (res, range) of
--    (Nothing, _) -> Nothing

d :: Char -> ReE Range x y -> ReE Range x y
d c (SymE Nothing) = EpsE (Sym c) -- c
d c (SymE (Just as))
    | c `elem` as = EpsE (Sym c) -- c
    | otherwise = NilE GotWrong
d c (AltE a b) = AltE (d c a) (d c b)
d c (CutE a b) = CutE (d c a) (d c b)
-- This one grows.
-- The top-most Alt can be done by our `unionCut`
-- can and has to be.
d c (SeqE a b) = union' (SeqE (d c a) b)
                        (SeqE (v a) (d c b))
-- This one used to grow.
-- but didn't have to.
-- equivalent to Seq a (Rep b)
d c (RepE a) = RepEM (d c a) a
-- $ FMap (uncurry (:)) $ Seq (d c a) (Rep a)
d c (RepEM a b) = case d c (SeqE a (RepE b)) of
    SeqE x (RepEM y z) -> RepEM (union' x y) z
-- Magic here.
d c (NotE a) = NotE (d c a)
-- Need to be able to represent Nil.
d _ (EpsE a) = NilE undefined -- TODO: define!
d _ (NilE y) = NilE y
-- d c (FMap f x) = FMap f (d c x)

-- Or do we need BoolBefore?
union' :: ReE a x y -> ReE a x y -> ReE a x y
union' = undefined

unionCut' :: forall f g h x y . (f -> g -> h) -> (f -> g -> h) -> ReE f x y -> ReE g x y -> ReE h x y
unionCut' (*) (+) = u where
    u :: forall x y . ReE f x y -> ReE g x y -> ReE h x y
    u (SymE x) (SymE y) = SymE $ x + y
    u (SymE x) (EpsE _) = undefined --- TODO.  We'll probably need a better reprentation.
    u (SymE x) (NilE _) = undefined --- TODO
    u (AltE x y) (AltE x' y') = AltE (u x x') (u y y')
    u (SeqE x y) (SeqE x' y') = SeqE (u x x') (u y y')
    u (CutE x y) (CutE x' y') = CutE (u x x') (u y y')
    -- NOTE: we swap (+) and (*).
    u (NotE x) (NotE x') = NotE $ unionCut' (+) (*) x x'
    u (RepE x) (RepE x') = RepE $ u x x'
    -- We have a choice here.  Doesn't matter too much what we do.
    -- Left biased by default.
    u (EpsE x) (EpsE x') = EpsE $ x
    u (NilE a) (NilE a') = (NilE a)


-- Is this some kind of (<*>)?  If yes, than on the first argument, not the last/second.
-- Can we abstract this repeated pattern?  (Something like uniplate, or scrap your boilerplate?)
-- Oh, NotX means we need an explicit & and | (swapping them, because of DeMorgan's law.)
unionCut :: forall f g h x . (f -> g -> h) -> (f -> g -> h) -> Re f x -> Re g x -> Re h x
unionCut (*) (+) = u where
    u :: forall x . Re f x -> Re g x -> Re h x
    u (SymX x) (SymX y) = SymX $ x + y
    u (AltX x y) (AltX x' y') = AltX (u x x') (u y y')
    u (SeqX x y) (SeqX x' y') = SeqX (u x x') (u y y')
    u (CutX x y) (CutX x' y') = CutX (u x x') (u y y')
    -- NOTE: we swap (+) and (*).
    u (NotX x) (NotX x') = NotX $ unionCut (+) (*) x x'
    u (RepX x) (RepX x') = RepX $ u x x'
    -- We have a choice here.  Doesn't matter too much what we do.
    -- Left biased by default.
    u (EpsX x) (EpsX x') = EpsX $ x
    u NilX NilX = NilX


union, cut :: Re BoolAfter x -> Re BoolAfter x -> Re BoolAfter x
union = unionCut (onBoolAfter (&&)) (onBoolAfter (||))
cut   = unionCut (onBoolAfter (||)) (onBoolAfter (&&))
onBoolAfter (*) (BoolAfter x) (BoolAfter y) = BoolAfter $ x * y
onBoolBefore (*) (BoolBefore x) (BoolBefore y) = BoolBefore $ x * y

data Evidence x where
    SymV :: Char -> Evidence Sym
    AltV :: Evidence x -> Evidence y -> Evidence (Alt x y)
    SeqV :: Evidence x -> Evidence y -> Evidence (Seq x y)
    CutV :: Evidence x -> Evidence y -> Evidence (Cut x y)
    -- Not?

-- How to describe, on the type level, the type to the left, and right of a
-- specific cursor / lens point.  Something with continuations?
-- Seq x y
-- left:
-- f y -> f (Seq x y)
-- f (Seq x y) -> f x
-- f (Seq x y) -> f y

-- cursor means = everything to the left is equivalent to eps.

isValid :: ReE f x y -> Evidence x -> Maybe String
isValid = undefined

extractString :: Evidence x -> Maybe String
extractString = undefined

prop_evidenceSeq :: Evidence x -> Evidence y -> Property
prop_evidenceSeq x y = ((++) <$> extractString x <*> extractString y)
    === extractString (SeqV x y)
-- But that's only at the top level.  That's somewhat disappointing.

check :: ReE f x y -> String -> Evidence x -> Bool
check = undefined

-- Can't type reverse in the general case..
reverse' :: Re f (Seq a b) -> Re f (Seq b a)
reverse' (SeqX a b) = (SeqX b a)

main = return ()

{-

Before = id
Eps
Nil

In the case of full expressions:
{ Before, Eps }
Nil = {}  -- empty
-- Is that true?

a e c
e b e
---- point-wise union /= union
a|e b|e c|e -- that's false

We could rescue the point-wise union by arguing that
in our cases it might work?  (We only ever produce things to union
via derivatives of one common expression.)

Let's see:  first, derivatives work from left to right.  Thus a e c is not
possible like this.


a (b|bc) c
e  e ec  c
match: abc
e  e ee  c \
e  e _   e - (c|e)

-- move through seq from left to right. (rep* complicates things..)

Let's produce and check evidence of match.  (and evidence of non-match in the other case.  equivalent, because of complement operator.)

-}
