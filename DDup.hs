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
import Control.Arrow ((***),(&&&))

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
instance Bifun (Phantom R) where bifun _ _ (Phantom x) = Phantom x

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


flattenForget :: (Uni r) => NF r f s -> r f s
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
instance (Bifun r, Uni r) => Bifun (NF r) where
    bifun ff sf = nfOp1 (bifun ff sf)

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
instance Functor (Count f) where fmap _ (Count i) = Count i
instance Bifun Count where bifun _ _ (Count i) = Count i

count :: Count f s -> Int
count (Count i) = i

x = sym Nothing
a = sym (Just "a")
b = sym (Just "b")

-- Wrap in newtype, if we ever have any problems.
instance Sym Either where sym range = Left Before
instance Uni Either where
    uni (Left _) r = r
    uni r@(Right _) _ = r
instance Alt Either where
    alt (Left l) (Left r) = Left (Cut l r)
    alt (Left _) (Right r) = Right (AltR r)
    alt (Right l) (Left _) = Right (AltL l)
    alt (Right l) (Right r) = Right (AltB l r)
instance Cut Either where
    cut (Left l) (Left r) = Left (AltB l r)
    cut (Left l) (Right _) = Left (AltL l)
    cut (Right _) (Left r) = Left (AltR r)
    cut (Right l) (Right r) = Right (Cut l r)
instance Seq Either where
    seq (Left l) (Left r) = Left (AltL l)
    seq (Left l) (Right _) = Left (AltL l)
    seq (Right l) (Left r) = Left (AltR (Seq l r))
    seq (Right l) (Right r) = Right (Seq l r)
instance Rep Either where rep _ = Right $ Rep []
instance Not Either where
    not (Left x) = Right x
    not (Right x) = Left x
instance Eps Either where eps = Right ()
instance Nil Either where nil = Left ()
instance Bifun Either where
    bifun ff _ (Left x) = Left $ ff x
    bifun _ sf (Right x) = Right $ sf x

-- instead of -> could also have something more inspectable.
data D r f s = D { unD :: Char -> r f s
                 , now :: r f s
                 , v :: Either f s}
dOp2 op1 op2 op3 (D d n v) (D d' n' v') = D (liftA2 op1 d d') (op2 n n') (op3 v v')
dOp1 op1 op2 op3 (D d n v) = D (liftA op1 d) (op2 n) (op3 v)

instance (Uni r) => Uni (D r) where uni = dOp2 uni uni uni
    
instance (Sym r, Bifun r, Nil r, Eps r) => Sym (D r) where
    sym range = D (\char -> case rangeMatch range char of
        Nothing -> bifun (const $ Wrong range char) id $ nil
        Just _ -> bifun (const $ TooMany) (const $ char) $ eps)
        (sym range)
        (sym range)
instance (Alt r) => Alt (D r) where alt = dOp2 alt alt alt
instance (Cut r) => Cut (D r) where cut = dOp2 cut cut cut
-- TODO: 
instance (Seq r, Uni r, Bifun r) => Seq (D r) where
    seq (D r n v) (D r' n' v') =
        D (case v of
            Left _ -> \c -> r c `seq` n'
            Right x -> \c -> (r c `seq` n') `uni`
                             (bifun (fc x) (sc x) $ r' c))
          (n `seq` n')
          (v `seq` v')
        where fc x f = AltR (Seq x f)
              -- seems somewhat fishy.
              sc x s = Seq x s
instance (Rep r, Uni r, Seq r, Bifun r) => Rep (D r) where
    rep (D r n v) = D
        (\c -> bifun fc sc $ r c `seq` rep n)
        (rep n)
        (rep v)
        -- TODO: How do we get more than one element in the list?
        where fc (AltL f) = Seq (Rep []) f
              fc (AltR (Seq x (Seq (Rep xs) f))) = Seq (Rep $ x:xs) f
              -- Shouldn't really happen.
              fc (AltB _ (Seq x (Seq (Rep xs) f))) = Seq (Rep $ x:xs) f
              -- TODO: How do we get more than two elements in the list?
              sc (Seq l (Rep r)) = Rep $ l : r
instance (Not r) => Not (D r) where
    not = dOp1 not not not
instance (Eps r, Nil r) => Eps (D r) where
    eps = D (const nil) eps eps
instance (Nil r) => Nil (D r) where
    nil = D (const nil) nil nil
instance (Functor (r f)) => Functor (D r f) where
    fmap fn = dOp1 (fmap fn) (fmap fn) (fmap fn)
instance (Bifun r) => Bifun (D r) where
    bifun ff sf = dOp1 (bifun ff sf) (bifun ff sf) (bifun ff sf)

-- add NF here.
d :: (Uni r) => Char -> D (NF r) f s -> r f s
d char (D r _ _) = flattenForget $ r char

newtype BackAll r f s = BackAll { unB :: D (NF (Both (BackAll r) r)) f s }
    deriving (Uni, Sym, Alt, Seq, Cut, Rep, Not, Nil, Eps, Bifun, Functor)


instance (Uni r, Nil r, Sym r, Seq r, Bifun r, Eps r) => IsString (BackAll r () [Char]) where
    fromString s = string s


dd :: [Char] -> BackAll Either f s -> Either f s
dd = dd'

-- TODO: investigate whether we can get by without the (Uni r) constraint
dd' :: (Uni r) => [Char] -> BackAll r f s -> r f s
dd' l re = two . flattenForget . now . unB
    $ foldl (\(BackAll (D r _ _)) c -> one . flattenForget $ r c) re l

-- aaa :: Either SymE Char
-- aaa = v . d 'b' . d 'a' $ a

result :: Either f s -> Either f s
result = id

main = do
    print $ forget' . flattenForget $ x `uni` x
    print $ forget' . flattenForget $ a `uni` (b `uni` x)
    print $ forget' . flattenForget $ a `uni` (b `uni` a)
    print $ forget' . flattenForget $ a `uni` (a `uni` b)
    print $ forget' . flattenForget $ a `uni` (a `uni` fmap undefined a)
    print $ forget' . flattenForget $ a
    let re = a
    print $ forget' . d 'a' $ a
    print $ dd "a" a
    print $ dd "ab" a
    print $ dd "" (rep $ string "abc")
    putStrLn "------"
    print $ dd "ababab" (rep $ string "ab")
    let ab = string "ab"
    print $ dd "ababab" (ab `seq` ab `seq` ab)
    print $ count $ dd' "ababab" (ab `seq` ab `seq` ab)
    let cf (Both c (Both f r)) = (count c, result f, forget' r)
    print $ cf $ dd' (concat $ replicate 50 "abc") (rep $ a `seq` b `seq` x)
