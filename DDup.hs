{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
import Final hiding (main)
import Control.Applicative hiding (empty)
import Control.Monad
import Prelude hiding (seq, not)
import qualified Prelude as P
import qualified Types as T
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Util
import Data.List
import Data.String
import Data.Biapplicative
import Data.Bifunctor
import Data.Function (on)
import Data.Ord
import Control.Arrow ((***))

newtype Phantom a f s = Phantom { forget :: a }
instance (Eq a) => Eq (Phantom a f s) where
        x == y = forget x == forget y
instance (Ord a) => Ord (Phantom a f s) where
        compare = comparing forget
p = Phantom

type R = T.Re' T.Range

-- helper:
(.:) f g a b = f (g a b)

wrap op x y = Phantom $ op (forget x) (forget y)
class Uni r where uni :: r f s -> r f s -> r f s
instance (Uni l, Uni r) => Uni (Both l r) where
    uni (Both l l') (Both r r') = Both (uni l r) (uni l' r')
instance Uni (Phantom R) where uni = wrap T.Uni'

instance Sym (Phantom R) where sym = p . T.Sym'
instance Alt (Phantom R) where alt = wrap T.Alt'
instance Cut (Phantom R) where cut = wrap T.Cut'
instance Seq (Phantom R) where seq = wrap T.Seq'
instance Rep (Phantom R) where rep = p . T.Rep' . forget
instance Not (Phantom R) where not = p . T.Rep' . forget
instance Eps (Phantom R) where eps = p T.Eps'
instance Nil (Phantom R) where nil = p T.Nil'
instance Functor (Phantom R f) where fmap f (Phantom x) = Phantom x

-- All uni's should be sorted, und unified, eg like Set.
-- muck around with contexts like for flattening in the paper?
data NF r f s = NF (Map (Phantom R f s) (r f s))
-- This is doing
-- a + a = a
-- a + b = b + a
-- but missing
-- (a + b) + c = a + (b + c)

nfOp op l r = NF $ Map.singleton key val where
    (Both key val) = op (flatten l) (flatten r)
nfOp1 op x = NF $ Map.singleton key val where
    (Both key val) = op (flatten x)

flattenForget = two . flatten
-- Only works on non-empty sets!
flatten :: (Uni r) => NF r f s -> Both (Phantom R) r f s
flatten (NF l) = foldr1 uni . map (uncurry Both) $ Map.toList l where

instance (Sym r) => Sym (NF r) where
    sym range = NF $ Map.singleton (sym range) (sym range)
instance  (Alt r, Uni r) => Alt (NF r) where alt = nfOp alt
instance  (Cut r, Uni r) => Cut (NF r) where cut = nfOp cut
instance  (Seq r, Uni r) => Seq (NF r) where seq = nfOp seq
instance (Rep r, Uni r) => Rep (NF r) where rep = nfOp1 rep
instance (Not r, Uni r) => Not (NF r) where not = nfOp1 not
instance (Eps r) => Eps (NF r) where
    eps = NF $ Map.singleton eps eps
instance (Nil r) => Nil (NF r) where
    nil = NF $ Map.singleton nil nil
instance (Functor (r f), Uni r) => Functor (NF r f) where
    fmap fn = nfOp1 (fmap fn)

instance (Uni r) => Uni (NF r) where
    uni (NF l) (NF r) = NF $ Map.union l r

forget' :: Phantom R f s -> R
forget' = forget

newtype Count f s = Count Int
plus (Count l) (Count r) = Count $ l + 1 + r

instance Uni Count where uni = plus
instance Sym Count where sym = const (Count 1)
instance Alt Count where alt = plus
instance Cut Count where cut = plus
instance Seq Count where seq = plus
instance Rep Count where rep (Count i) = Count $ 1+i
instance Not Count where not (Count i) = Count $ 1+1
instance Eps Count where eps = (Count 1)
instance Nil Count where nil = (Count 1)
instance Functor (Count f) where fmap _ (Count i) = (Count i) 

count :: Count f s -> Int
count (Count i) = i

x = sym Nothing
a = sym (Just "a")
b = sym (Just "b")

-- newtype Derivative f s

main = do
    print $ count . flattenForget $ x `uni` x
    print $ count . flattenForget $ a `uni` (b `uni` x)
    print $ count . flattenForget $ a `uni` (b `uni` a)
    print $ count . flattenForget $ a `uni` (a `uni` b)
    print $ count . flattenForget $ a `uni` (a `uni` fmap id a)
