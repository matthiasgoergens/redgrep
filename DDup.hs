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
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ViewPatterns #-}
import Final hiding (main)
import Tool
import ArbitraryFinal
import Data.Bifunctor
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
import Data.Function (on)
import Data.Ord
import Control.Arrow ((***),(&&&))
import Test.QuickCheck

-- All uni's should be sorted, und unified, eg like Set.
-- muck around with contexts like for flattening in the paper?
-- -- Map should be non-empty, but have no Nils, and no-single eps.
data NF r f s
    -- = IsBimap ff sf (NF r f s)
    = IsEps f s | IsNil f | NF (Map (Phantom R f s) (Both Either r f s))
    -- deriving (Show)
-- This is doing
-- a + a = a
-- a + b = b + a
-- (a + b) + c = a + (b + c)

-- Try floating fmaps only first.
data NFMap r f s
    = forall f' s' . NFMap (f' -> f) (s' -> s) (r f' s')
    | ID (r f s)

un :: Bifunctor r => NFMap r f s -> r f s
un (NFMap f s x) = bimap f s x
un (ID r) = r

nfmap :: r f s -> NFMap r f s
nfmap = ID

nfmap' (ID x) = NFMap id id x
nfmap' x = x

instance Bifunctor (NFMap r) where
    -- whole point of NFMap
    bimap ff sf (nfmap' -> NFMap f s x) = NFMap (ff . f) (sf . s) x
-- other instances are pretty trivial:
instance Functor (NFMap r f) where
    fmap = bimap id

onUn op x y = ID $ op (un x) (un y)
instance (Bifunctor r, Uni r) => Uni (NFMap r) where
    uni = onUn uni
instance (Bifunctor r, RE r) => RE (NFMap r) where
    sym = ID . sym
    alt = onUn alt
    cut = onUn cut
    seq = onUn seq
    rep = ID . rep . un
    not = ID . not . un
    eps = ID .: eps
    nil = ID . nil

nfOp op l r = NF $ Map.singleton sortKey fullValue where
    (Both sortKey fullValue) = op (flatten l) (flatten r)
nfOp1 op x = NF $ Map.singleton key val where
    (Both key val) = op (flatten x)

nf :: NF r f s -> NF r f s
nf = id

flattenForget :: (Uni r, Bifunctor r, RE r) => NF r f s -> r f s
flattenForget = two . two . flatten
-- Only works on non-empty maps!
-- TODO: filter out the nils, too.
flatten :: (Uni r, Bifunctor r, RE r) => NF r f s -> Both (Phantom R) (Both Either r) f s
flatten (NF l) = foldr1 uni . map (uncurry Both) $ Map.toList $ l where
flatten (IsNil f) = nil f
flatten (IsEps f s) = eps f s

instance (Bifunctor r, RE r, Uni r) => RE (NF r) where
    sym range = NF $ Map.singleton (sym range) (sym range)

    alt (IsNil f) (IsNil f') = nil (Cut f f')
    alt (IsNil f) r = bimap (Cut f) AltR r
    alt l (IsNil f) = bimap (`Cut` f) AltL l
    alt x y = nfOp alt x y

    -- Left biased.
    cut (IsNil f) _ = nil (AltL f)
    cut _ (IsNil f) = nil (AltR f)
    -- cut (IsEps _ _) (Both (Left f) _) = IsNil $ AltR f
    -- cut (IsEps f s) (NF (Both (Right s') _)) = eps (AltL f) (Cut s s')
    
    -- cut (Both (Left f) _)   (IsEps _ _) = IsNil $ AltL f
    -- cut (Both (Right s') _) (IsEps f s) = IsEps (AltL f) (Cut s s')
    cut x y = nfOp cut x y

    seq (IsNil f) _ = nil (AltL f)
-- turns success into failure, too..  But gives an interesting error message..
-- shoudn't happen, in any case..
--    seq x (IsNil f) = bimap (const $ AltR
    seq (IsEps f s) (IsEps f' s') = eps (AltR $ Seq s f') (Seq s s')
    seq (IsEps f s) r = bimap (AltR . Seq s)  (Seq s) r
    seq l (IsEps f s) = bimap AltL (`Seq` s) l
    seq x y = nfOp seq x y

    rep (IsNil f) = eps (Seq (Rep []) f) (Rep [])
    rep (IsEps f _) = eps (Seq (Rep []) f) (Rep [])
    rep x = nfOp1 rep x

    not = nfOp1 not

    eps = IsEps
    -- eps = NF $ Map.singleton eps eps

    nil = IsNil
instance (Uni r, Bifunctor r, RE r) => Functor (NF r f) where
    fmap fn = bimap id fn
instance (Uni r, Bifunctor r, RE r) => Bifunctor (NF r) where
    bimap ff _ (IsNil f) = IsNil $ ff f
    bimap ff sf (IsEps f s) = IsEps (ff f) (sf s)
    bimap ff sf x = nfOp1 (bimap ff sf) x

-- The whole point of this NF exercise:
instance (Uni r, RE r, Bifunctor r) => Uni (NF r) where
    uni (NF l) (NF r) = NF $ Map.union l r
    uni (NF l) (IsEps f s) = NF $ Map.insert
        (eps undefined undefined) (eps f s) l
    uni (IsEps f s) (NF l) = NF $ Map.insert
        (eps undefined undefined) (eps f s) l
    uni l@(IsEps _ _) (IsEps _ _) = l
    uni (IsNil _) r = r
    uni l (IsNil _) = l
    
forget' :: Phantom R f s -> R
forget' = forget

newtype Count f s = Count Int
    deriving (Show, Eq, Ord)
plus (Count l) (Count r) = Count $ l + 1 + r

instance Uni Count where uni = plus
instance RE Count where
    sym = const (Count 1)
    alt = plus
    cut = plus
    seq = plus
    rep (Count i) = Count $ 1+i
    not (Count i) = Count $ 1+1
    eps _ _ = Count 1
    nil _ = Count 1
instance Functor (Count f) where fmap _ (Count i) = Count i
instance Bifunctor Count where bimap _ _ (Count i) = Count i

count :: Count f s -> Int
count (Count i) = i

x = sym Nothing
xx = Rep' (Seq' (Not' Eps') (Not' Nil'))
a = sym (Just "a")
b = sym (Just "b")

-- Wrap in newtype, if we ever have any problems.
instance Uni Either where
    uni (Left _) r = r
    uni r@(Right _) _ = r
instance RE Either where
    sym range = Left Before

    alt (Left l) (Left r) = Left (Cut l r)
    alt (Left _) (Right r) = Right (AltR r)
    -- left biased.
    alt (Right l) _ = Right (AltL l)

    -- left biased on error.
    cut (Left l) _ = Left (AltL l)
    cut _ (Left r) = Left (AltR r)
    cut (Right l) (Right r) = Right (Cut l r)

    seq (Left l) (Left r) = Left (AltL l)
    seq (Left l) (Right _) = Left (AltL l)
    seq (Right l) (Left r) = Left (AltR (Seq l r))
    seq (Right l) (Right r) = Right (Seq l r)

    rep _ = Right $ Rep []

    not (Left x) = Right x
    not (Right x) = Left x

    eps _ = Right
    nil = Left

-- instead of -> could also have something more inspectable.
data D r f s = D { unD :: Char -> r f s
                 , now :: r f s
                 , v :: Either f s }
dOp2 op1 op2 op3 (D d n v) (D d' n' v') = D (liftA2 op1 d d') (op2 n n') (op3 v v')
dOp1 op1 op2 op3 (D d n v) = D (liftA op1 d) (op2 n) (op3 v)

instance (Uni r) => Uni (D r) where uni = dOp2 uni uni uni
    
instance (Uni r, Bifunctor r, RE r) => RE (D r) where
    sym range = D (\char -> case rangeMatch range char of
        Nothing -> nil (Wrong range char)
        Just _ -> eps TooMany char)
        (sym range)
        (sym range)

    alt = dOp2 alt alt alt
    cut = dOp2 cut cut cut

-- Might need Uni?
-- TODO: 
    seq (D r n v) (D r' n' v') =
        D (\c -> either (flip const) (uni . f c) v
                    (r c `seq` n'))
          (n `seq` n')
          (v `seq` v')
        where
            f c x = bimap (AltR . Seq x) (Seq x) $ r' c
    rep (D r n v) = D
        (\c -> bimap fc sc $ r c `seq` rep n)
        (rep n)
        (rep v)
        -- TODO: How do we get more than one element in the list?
        where fc (AltL f) = Seq (Rep []) f
              fc (AltR (Seq x (Seq (Rep xs) f))) = Seq (Rep $ x:xs) f
              -- TODO: How do we get more than two elements in the list?
              sc (Seq l (Rep r)) = Rep $ l : r

    not = dOp1 not not not
    eps f s = D (const $ nil f) (eps f s) (eps f s)
    nil f = D (const $ nil f) (nil f) (nil f)

instance (Functor (r f)) => Functor (D r f) where
    fmap fn = dOp1 (fmap fn) (fmap fn) (fmap fn)
instance (Bifunctor r) => Bifunctor (D r) where
    bimap ff sf = dOp1 (bimap ff sf) (bimap ff sf) (bimap ff sf)

d :: (Uni r, Bifunctor r, RE r) => Char -> D (NF r) f s -> r f s
d char (D r _ _) = flattenForget $ r char

newtype BackAll r f s = BackAll { unB :: D (NF (NFMap (Both (BackAll r) r))) f s }
    deriving (Uni, RE, Bifunctor, Functor)

unBackAll :: (Bifunctor r, RE r, Uni r) => BackAll r f s -> r f s
unBackAll = two . un . flattenForget . now . unB

instance (Uni r, Bifunctor r, RE r) => IsString (BackAll r () [Char]) where
    fromString s = string s

dd :: [Char] -> BackAll Either f s -> Either f s
dd = dd'

d1 :: (Bifunctor r, RE r, Uni r) => Char -> BackAll r f s -> BackAll r f s
d1 c = one . un . flattenForget . ($c) . unD . unB

-- TODO: investigate whether we can get by without the (Uni r) constraint
dd' :: (Uni r, Bifunctor r, RE r) => [Char] -> BackAll r f s -> r f s
dd' l re = unBackAll $ foldl (flip d1) re l

dd_ :: (Uni r, Bifunctor r, RE r) => [Char] -> BackAll r f s -> [r f s]
dd_ l re = map unBackAll $ scanl (flip d1) re l

-- aaa :: Either SymE Char
-- aaa = v . d 'b' . d 'a' $ a

result :: Either f s -> Either f s
result = id

nf' :: NF Count f s -> NF Count f s
nf' = id

nilX, nilY :: (Bifunctor r, RE r) => r SymE Char
nilX = nil TooMany
nilY = nil Before

print3 (a,b,c) = print a >> print b >> print c >> putStrLn ""

-- mainOld = do
--     print $ nf' $ x `uni` (flip uni nilX nilY)
--     print $ nf' $ nilX `uni` x
-- 
--     print $ nf' $ x `seq` nilX
--     print $ nf' $ nilX `seq` x
-- 
--     print $ nf' $ x `cut` nilX
--     print $ nf' $ nilX `cut` x
-- 
--     print $ nf' $ nilX `alt` x
--     print $ nf' $ x `alt` nilX
-- 
--     print $ nf' $ eps () () `seq` x
--     print $ nf' $ x `seq` eps () ()
--     putStrLn "+++++"
--     main'
-- main'' = do
--     putStrLn "------"
--     print $ forget' . flattenForget $ x `uni` x
--     print $ forget' . flattenForget $ a `uni` (b `uni` x)
--     print $ forget' . flattenForget $ a `uni` (b `uni` a)
--     print $ forget' . flattenForget $ a `uni` (a `uni` b)
--     print $ forget' . flattenForget $ a `uni` (a `uni` fmap undefined a)
--     print $ forget' . flattenForget $ a
-- main' = do
--     let re = a
--     print $ forget' . d 'a' $ a
--     print $ dd "a" a
--     print $ dd "ab" a
--     print $ dd "" (rep $ string "abc")
--     putStrLn "------"
--     print $ dd "ababab" (rep $ string "ab")
--     let ab = string "ab"
--     print $ dd "ababab" (ab `seq` ab `seq` ab)
--     print $ count $ dd' "ababab" (ab `seq` ab `seq` ab)
--     let cf (Both c (Both f r)) = (count c, result f, forget' r)
--     print $ cf $ dd' (concat $ replicate 50 "abc") (rep $ string "abc")
--     let flapping = cut (i `seq` string "ping") (not $ i `seq` string "flapping") `seq` i
--     putStrLn "Flapping!"
--     putStrLn ""
--     print3 $ cf $ dd' "ee flapping eue" flapping
--     print3 $ cf $ dd' "ee flapping eue ping oe" flapping
--     print3 $ cf $ dd' "ee lapping eue pin" flapping
--     -- Quadratic! Rep takes quadratic time!
--     -- print3 $ cf $ dd' (concat $ replicate 10000 "a") (rep $ sym Nothing)
--     -- print3 $ cf $ dd' (concat $ replicate 1250 "a") (rep $ sym Nothing)
-- sain = do
--     let i = 20
--     let rex = dd' (concat $ replicate i "a") $
--                     bimap (const ()) (const ())
--                     $ not nil_ `seq` not nil_
--     -- print $ count rex
--     -- print $ nf' rex
--     return ()
-- 
-- fain i = do
--     -- quadratic again..
--     print $ ((count *** result) . unBoth *** forgetF) . unBoth $
--     -- print $ count $
--         dd' (concat $ replicate i "ab") $
--             bimap (const ()) id
--             $ cut (not nil_ `seq` not nil_) 
--                   (rep $ sym Nothing)
--             `seq` (sym (Just "ab"))
--     -- print3 $ cf $ dd' (concat $ replicate 2500 "a") (rep $ sym Nothing)

inti :: r Int Int -> r Int Int
inti = id
prop_or (inti . run -> rx) (inti . run -> ry) s =
    case (dd s rx, dd s ry, dd s (alt rx ry)) of
        (Left x, Left y, Left xy) -> Cut x y === xy
        (Right x, _, Right x') -> AltL x === x'
        (_, Right y, Right y') -> AltR y === y'
        ((x :: Either Int Int), y, z) -> counterexample (unwords ["Something's wrong: ", show x, show y, show z]) $ False

prop_or' (Shield (run -> rx)) (Shield (run -> ry)) s =
    case (dd s rx, dd s ry, dd s (alt rx ry)) of
        (Left _, Left _, Left (Cut _ _)) -> True
        (Right _, _, Right (AltL _)) -> True
        (_, Right y, Right (AltR _)) -> True
        otherwise -> False

prop_and (inti . run -> rx) (inti . run -> ry) s =
     case (dd s rx, dd s ry, dd s (cut rx ry)) of
        (Left x, _, Left (AltL xy)) -> x === xy
        -- Really?
        (_, Left y, Left (AltR xy)) -> y === xy
        (Right _, Left y, Left y') -> AltR y === y'
        (Right x, Right y, Right y') -> Cut x y === y'
        ((x :: Either Int Int), y, z) -> counterexample (unwords ["Something's wrong: ", show x, show y, show z]) $ False

prop_and' (Shield (run -> rx)) (Shield (run -> ry)) s =
    let dx = dd' s rx
        dy = dd' s ry
        dxy = dd' s (cut rx ry)
        show' (Left _) = "left"
        show' (Right _) = "right"
    in case (dx, dy, dxy) of
        (Left x, Left y, Left (AltL xy)) -> 1 === 1
        -- Really?
        (Left x, Left y, Left (AltR xy)) -> 1 === 1
        (Right _, Left y, Left (AltR y')) -> 1 === 1
        (Left x, Right y, Left (AltL xy)) -> 1 === 1
        (Right x, Right y, Right (Cut _ _)) -> 1 === 1
        (blunt -> x, blunt -> y, bimap blunt blunt -> xy) -> counterexample (unwords [show x, show y, show xy]) False

prop_not' (Shield (run -> r)) s =
    blunt (dd s r) === switch (blunt $ dd s (not r))

-- Rep' (Seq' (Sym' Nothing) (Rep' (Not' Nil')))
-- Rep' (Alt' (Not' Nil') (Sym' Nothing))
problem = toShield $ Rep' (Rep' (Not' (Sym' Nothing)))
-- problem = toShield $ (Rep' (Not' (Sym' Nothing)))

problemify = case problem of Shield r -> map (r' . forget) $ dd_ (repeat 'a') $ run r

prop_size :: Shield REini -> Property
prop_size (Shield r) =
    count (run r) < 50 ==>
    null . dropWhile (<5000) . take 100 . map count $ dd_ (repeat 'a') (run r)

i = rep (sym Nothing)

main = do
    -- mapM_ fain [100]
    sample (forgetF . un . flattenForget . run <$> (arbitrary :: Gen (REini Int Int)))
    verboseCheck prop_size

mainTests = do
    putStrLn ""
    putStrLn "prop_and'"
    verboseCheck prop_and'
--    putStrLn ""
--    putStrLn "prop_and"
--    quickCheck prop_and
    putStrLn ""
    putStrLn "prop_or'"
    verboseCheck prop_or'
--    putStrLn ""
--    putStrLn "prop_or"
--    quickCheck prop_or
    putStrLn ""
    putStrLn "prop_not'"
    verboseCheck prop_not'
