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
import Final hiding (main)
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

newtype Phantom a f s = Phantom { forget :: a }
instance (Eq a) => Eq (Phantom a f s) where
        x == y = forget x == forget y
instance (Ord a) => Ord (Phantom a f s) where
        compare = comparing forget
instance (Show a) => Show (Phantom a f s) where
    show = show . forget
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
instance Not (Phantom R) where not = p . T.Not' . forget
instance Eps (Phantom R) where eps = p T.Eps'
instance Nil (Phantom R) where nil = p T.Nil'
instance Functor (Phantom R f) where fmap _ (Phantom x) = Phantom x
instance Bifunctor (Phantom R) where bimap _ _ (Phantom x) = Phantom x

type Rf = Re'f T.Range
instance Uni (Phantom Rf) where uni = wrap Uni'
instance Sym (Phantom Rf) where sym = p . Sym'
instance Alt (Phantom Rf) where alt = wrap Alt'
instance Cut (Phantom Rf) where cut = wrap Cut'
instance Seq (Phantom Rf) where seq = wrap Seq'
instance Rep (Phantom Rf) where rep = p . Rep' . forget
instance Not (Phantom Rf) where not = p . Not' . forget
instance Eps (Phantom Rf) where eps = p Eps'
instance Nil (Phantom Rf) where nil = p Nil'
instance Functor (Phantom Rf f) where fmap _ (Phantom x) = Phantom (Bimap' x)
instance Bifunctor (Phantom Rf) where bimap _ _ (Phantom x) = Phantom (Bimap' x)

data Re'f f = Sym' f | Alt' (Re'f f) (Re'f f) | Cut' (Re'f f) (Re'f f)
           | Seq' (Re'f f) (Re'f f) | Rep' (Re'f f) | Not' (Re'f f)
           | Eps' | Nil'
           | Uni' (Re'f f) (Re'f f) -- (Set.Set (Re'f f))
           | Bimap' (Re'f f)
    deriving (Eq, Ord, Show)


-- All uni's should be sorted, und unified, eg like Set.
-- muck around with contexts like for flattening in the paper?
-- -- Map should be non-empty, but have no Nils, and no-single eps.
data NF r f s
    -- = IsBimap ff sf (NF r f s)
    = IsEps f s | IsNil f | NF (Map (Phantom R f s) (r f s))
    deriving (Show)
-- This is doing
-- a + a = a
-- a + b = b + a
-- (a + b) + c = a + (b + c)

-- Try floating fmaps only first.
data NFMap r f s
    = forall f' s' . NFMap (f' -> f) (s' -> s) (r f' s')
    | ID (r f s)
data NFMapFinal r f s
    = forall f' s' . NFMapFinal
        (((f'->f) -> (s'->s) -> r f s)
        -> r f s)

un :: Bifunctor r => NFMap r f s -> r f s
un (NFMap f s x) = bimap f s x
un (ID r) = r

nfmap :: r f s -> NFMap r f s
nfmap = ID

nfmap' (ID x) = NFMap id id x
nfmap' x = x

instance Sym r => Sym (NFMap r) where
    sym = ID . sym
-- TODO: How do you abstract these?
instance (Bifunctor r, Alt r) => Alt (NFMap r) where
    alt (un -> x) (un -> y) = ID $ alt x y
    alt (ID x) (ID y) = ID $ alt x y
    -- got a choice, could also choose ID.
    alt (nfmap' -> NFMap fx sx x) (nfmap' -> NFMap fy sy y) =
        NFMap (bimap fx fy) (bimap sx sy) $ alt x y
instance (Bifunctor r, Uni r) => Uni (NFMap r) where
    uni (un -> x) (un -> y) = ID $ x `uni` y
instance (Bifunctor r, Cut r) => Cut (NFMap r) where
    cut (un -> x) (un -> y) = ID $ cut x y
    cut (ID x) (ID y) = ID $ cut x y
    cut (nfmap' -> NFMap fx sx x) (nfmap' -> NFMap fy sy y) =
        NFMap (bimap fx fy) (bimap sx sy) $ cut x y
instance (Bifunctor r, Seq r) => Seq (NFMap r) where
    seq (un -> x) (un -> y) = ID $ seq x y
    seq (ID x) (ID y) = ID $ seq x y
    seq (nfmap' -> NFMap fx sx x) (nfmap' -> NFMap fy sy y) =
        NFMap (bimap fx $ bimap sx fy) (bimap sx sy) $ seq x y
instance (Bifunctor r, Rep r) => Rep (NFMap r) where
    rep (un -> x) = ID $ rep x
    rep (ID x) = ID $ rep x
    rep (NFMap fx sx x) = NFMap (bimap (fmap sx) fx) (fmap sx) $ rep x
instance (Bifunctor r, Not r) => Not (NFMap r) where
    not (un -> x) = ID $ not x
    not (ID x) = ID $ not x
    not (NFMap fx sx x) = NFMap sx fx $ not x
instance (Eps r) => Eps (NFMap r) where
    eps = ID eps
instance (Nil r) => Nil (NFMap r) where
    nil = ID nil
instance Functor (NFMap r f) where
    fmap = bimap id
instance Bifunctor (NFMap r) where
    -- whole point..
    bimap ff sf (nfmap' -> NFMap f s x) = NFMap (ff . f) (sf . s) x

nfOp op l r = NF $ Map.singleton key val where
    (Both key val) = op (flatten l) (flatten r)
nfOp1 op x = NF $ Map.singleton key val where
    (Both key val) = op (flatten x)

nf :: NF r f s -> NF r f s
nf = id

flattenForget :: (Uni r, Bifunctor r, Nil r, Eps r) => NF r f s -> r f s
flattenForget = two . flatten
-- Only works on non-empty maps!
-- TODO: filter out the nils, too.
flatten :: (Uni r, Bifunctor r, Nil r, Eps r) => NF r f s -> Both (Phantom R) r f s
flatten (NF l) = foldr1 uni . map (uncurry Both) $ Map.toList l where
flatten (IsNil f) = nil_ f
flatten (IsEps f s) = eps_ f s

instance (Sym r) => Sym (NF r) where
    sym range = NF $ Map.singleton (sym range) (sym range)
instance  (Alt r, Uni r, Bifunctor r, Nil r, Eps r) => Alt (NF r) where
    alt (IsNil f) (IsNil f') = nil_ (Cut f f')
    alt (IsNil f) r = bimap (Cut f) AltR r
    alt l (IsNil f) = bimap (`Cut` f) AltL l
    alt x y = nfOp alt x y
instance  (Cut r, Uni r, Bifunctor r, Nil r, Eps r) => Cut (NF r) where
    -- Left biased.
    cut (IsNil f) _ = nil_ (AltL f)
    cut _ (IsNil f) = nil_ (AltR f)
    cut x y = nfOp cut x y
instance  (Seq r, Uni r, Bifunctor r, Nil r, Eps r) => Seq (NF r) where
    seq (IsNil f) _ = nil_ (AltL f)
-- turns success into failure, too..  But gives an interesting error message..
-- shoudn't happen, in any case..
--    seq x (IsNil f) = bimap (const $ AltR
    seq (IsEps f s) (IsEps f' s') = eps_ (AltR $ Seq s f') (Seq s s')
    seq (IsEps f s) r = bimap (AltR . Seq s)  (Seq s) r
    seq l (IsEps f s) = bimap AltL (`Seq` s) l
    seq x y = nfOp seq x y
instance (Rep r, Uni r, Bifunctor r, Nil r, Eps r) => Rep (NF r) where
    rep (IsNil f) = eps_ (Seq (Rep []) f) (Rep [])
    rep (IsEps f _) = eps_ (Seq (Rep []) f) (Rep [])
    rep x = nfOp1 rep x
instance (Not r, Uni r, Bifunctor r, Nil r, Eps r) => Not (NF r) where not = nfOp1 not
instance (Eps r, Bifunctor r) => Eps (NF r) where
    eps = IsEps () ()
    -- eps = NF $ Map.singleton eps eps
instance (Nil r) => Nil (NF r) where
    nil = IsNil ()
instance (Uni r, Bifunctor r, Nil r, Eps r) => Functor (NF r f) where
    fmap fn = bimap id fn
instance (Bifunctor r, Uni r, Nil r, Eps r) => Bifunctor (NF r) where
    bimap ff _ (IsNil f) = IsNil $ ff f
    bimap ff sf (IsEps f s) = IsEps (ff f) (sf s)
    bimap ff sf x = nfOp1 (bimap ff sf) x

-- The whole point of this NF exercise:
instance (Uni r, Eps r, Bifunctor r) => Uni (NF r) where
    uni (NF l) (NF r) = NF $ Map.union l r
    uni (NF l) (IsEps f s) = NF $ Map.insert
        (eps_ undefined undefined) (eps_ f s) l
    uni (IsEps f s) (NF l) = NF $ Map.insert
        (eps_ undefined undefined) (eps_ f s) l
    uni l@(IsEps _ _) (IsEps _ _) = l
    uni (IsNil _) r = r
    uni l (IsNil _) = l
    
forget' :: Phantom R f s -> R
forget' = forget

forgetF :: Phantom Rf f s -> Rf
forgetF = forget

newtype Count f s = Count Int
    deriving (Show, Eq, Ord)
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
instance Bifunctor Count where bimap _ _ (Count i) = Count i

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
    -- left biased.
    alt (Right l) _ = Right (AltL l)
instance Cut Either where
    -- left biased.
    cut (Left l) _ = Left (AltL l)
    cut _ (Left r) = Left (AltR r)
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

-- instead of -> could also have something more inspectable.
data D r f s = D { unD :: Char -> r f s
                 , now :: r f s
                 , v :: Either f s }
dOp2 op1 op2 op3 (D d n v) (D d' n' v') = D (liftA2 op1 d d') (op2 n n') (op3 v v')
dOp1 op1 op2 op3 (D d n v) = D (liftA op1 d) (op2 n) (op3 v)

instance (Uni r) => Uni (D r) where uni = dOp2 uni uni uni
    
instance (Sym r, Bifunctor r, Nil r, Eps r) => Sym (D r) where
    sym range = D (\char -> case rangeMatch range char of
        Nothing -> nil_ (Wrong range char)
        Just _ -> eps_ TooMany char)
        (sym range)
        (sym range)
instance (Alt r) => Alt (D r) where alt = dOp2 alt alt alt
instance (Cut r) => Cut (D r) where cut = dOp2 cut cut cut
-- TODO: 
instance (Seq r, Uni r, Bifunctor r) => Seq (D r) where
    seq (D r n v) (D r' n' v') =
        D (case v of
            Left _ -> \c -> r c `seq` n'
            Right x -> \c -> (r c `seq` n') `uni`
                             (bimap (fc x) (sc x) $ r' c))
          (n `seq` n')
          (v `seq` v')
        where fc x f = AltR (Seq x f)
              -- seems somewhat fishy.
              sc x s = Seq x s
instance (Rep r, Uni r, Seq r, Bifunctor r) => Rep (D r) where
    rep (D r n v) = D
        (\c -> bimap fc sc $ r c `seq` rep n)
        (rep n)
        (rep v)
        -- TODO: How do we get more than one element in the list?
        where fc (AltL f) = Seq (Rep []) f
              fc (AltR (Seq x (Seq (Rep xs) f))) = Seq (Rep $ x:xs) f
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
instance (Bifunctor r) => Bifunctor (D r) where
    bimap ff sf = dOp1 (bimap ff sf) (bimap ff sf) (bimap ff sf)

d :: (Uni r, Bifunctor r, Nil r, Eps r) => Char -> D (NF r) f s -> r f s
d char (D r _ _) = flattenForget $ r char

newtype BackAll r f s = BackAll { unB :: D (NF (NFMap (Both (BackAll r) r))) f s }
    deriving (Uni, Sym, Alt, Seq, Cut, Rep, Not, Nil, Eps, Bifunctor, Functor)

unBackAll :: (Bifunctor r, Nil r, Eps r, Uni r) => BackAll r f s -> r f s
unBackAll = two . un . flattenForget . now . unB

instance (Uni r, Nil r, Sym r, Seq r, Bifunctor r, Eps r) => IsString (BackAll r () [Char]) where
    fromString s = string s

dd :: [Char] -> BackAll Either f s -> Either f s
dd = dd'

d1 :: (Bifunctor r, Nil r, Eps r, Uni r) => Char -> BackAll r f s -> BackAll r f s
d1 c = one . un . flattenForget . ($c) . unD . unB

-- TODO: investigate whether we can get by without the (Uni r) constraint
dd' :: (Uni r, Bifunctor r, Nil r, Eps r) => [Char] -> BackAll r f s -> r f s
dd' l re = unBackAll $ foldl (flip d1) re l

-- aaa :: Either SymE Char
-- aaa = v . d 'b' . d 'a' $ a

result :: Either f s -> Either f s
result = id

nf' :: NF Count f s -> NF Count f s
nf' = id

nilX, nilY :: (Bifunctor r, Nil r) => r SymE Char
nilX = nil_ TooMany
nilY = nil_ Before

print3 (a,b,c) = print a >> print b >> print c >> putStrLn ""

mainOld = do
    print $ nf' $ x `uni` (flip uni nilX nilY)
    print $ nf' $ nilX `uni` x

    print $ nf' $ x `seq` nilX
    print $ nf' $ nilX `seq` x

    print $ nf' $ x `cut` nilX
    print $ nf' $ nilX `cut` x

    print $ nf' $ nilX `alt` x
    print $ nf' $ x `alt` nilX

    print $ nf' $ eps `seq` x
    print $ nf' $ x `seq` eps
    putStrLn "+++++"
    main'
main'' = do
    putStrLn "------"
    print $ forget' . flattenForget $ x `uni` x
    print $ forget' . flattenForget $ a `uni` (b `uni` x)
    print $ forget' . flattenForget $ a `uni` (b `uni` a)
    print $ forget' . flattenForget $ a `uni` (a `uni` b)
    print $ forget' . flattenForget $ a `uni` (a `uni` fmap undefined a)
    print $ forget' . flattenForget $ a
main' = do
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
    print $ cf $ dd' (concat $ replicate 50 "abc") (rep $ string "abc")
    let flapping = cut (i `seq` string "ping") (not $ i `seq` string "flapping") `seq` i
    putStrLn "Flapping!"
    putStrLn ""
    print3 $ cf $ dd' "ee flapping eue" flapping
    print3 $ cf $ dd' "ee flapping eue ping oe" flapping
    print3 $ cf $ dd' "ee lapping eue pin" flapping
    -- Quadratic! Rep takes quadratic time!
    -- print3 $ cf $ dd' (concat $ replicate 10000 "a") (rep $ sym Nothing)
    -- print3 $ cf $ dd' (concat $ replicate 1250 "a") (rep $ sym Nothing)
main = do
    mapM_ fain [10000]
    let i = 20
    let rex = dd' (concat $ replicate i "a") $
                    bimap (const ()) (const ())
                    $ (not nil `seq` not nil) 
    -- print $ count rex
    -- print $ nf' rex
    return ()

fain i = do
    -- quadratic again..
    print $ (count *** forgetF) . unBoth $
    -- print $ count $
        dd' (concat $ replicate i "a") $
            bimap (const ()) (const ())
            $ (not nil `seq` not nil) 
            -- (rep $ sym Nothing)
    -- print3 $ cf $ dd' (concat $ replicate 2500 "a") (rep $ sym Nothing)


i = rep (sym Nothing)
