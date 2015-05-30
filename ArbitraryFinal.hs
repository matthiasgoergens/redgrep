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
{-# LANGUAGE StandaloneDeriving #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}

module ArbitraryFinal (ArbWrap(..), Shield(..), toShield, altS, cutS, notS, uniS
    , example, s) where
import Prelude hiding (seq, not)
import qualified Prelude as P

import Final
import Test.QuickCheck
import Data.Bifunctor

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

import Test.QuickCheck
import Test.QuickCheck.Function
import Test.QuickCheck.All

infixr 9 .:
(.:) f g a b = f (g a b)

newtype ArbWrap r = ArbWrap { unwrap :: Both (Phantom Rf) r Int Int }
instance Show (ArbWrap r) where
    show = show . one . unwrap

instance Arbitrary (Shield REini) where
    arbitrary = Shield <$> arb
    shrink = shrinkS

instance Arbitrary (REini Int Int) where
    arbitrary = arb
    shrink = shrink'
a = ArbWrap

example = Bimap' (Rep' (Bimap' (Alt' (Bimap' (Not' (Bimap' (Alt' (Bimap' (Rep' (Bimap' (Sym' Nothing)))) (Bimap' (Sym' Nothing)))))) (Bimap' (Rep' (Bimap' (Alt' (Bimap' (Cut' (Bimap' (Sym' (Just ""))) (Bimap' (Cut' (Bimap' (Alt' Eps' (Bimap' (Not' Eps')))) Eps')))) (Bimap' (Rep' (Bimap' (Not' Eps')))))))))))
s = "\217\&5\226:J\ETX@<or7W>)\133c\162s\254\177\173\DELGO"


-- arbS :: RE r => Gen (Shield r)
-- arbS = fmap Shield . sized $ \n ->
--     let simple = [ bimap <$> arbitrary <*> arbitrary <*> (sym <$> arbitrary)
--                  , eps <$> arbitrary <*> arbitrary
--                  , nil <$> arbitrary ]
--         r1 = resize (n-1)
--         r2 = resize (n `div` 2)
--         on2 op = r2 $ bimap <$> arbitrary <*> arbitrary <*>  
--             (op <$> arb <*> arb)
--         on1 op = r1 $ bimap <$> arbitrary <*> arbitrary <*> (op <$> arb)
--         complex = [ on2 alt, on2 cut, on2 seq, on1 rep, on1 not ]
--     in if n <= 0
--     then oneof simple
--     else oneof $ simple ++ complex


arb :: forall r . RE r => Gen (r Int Int)
arb = sized $ \n ->
    let simple = [ bimap <$> arbitrary <*> arbitrary <*> (sym <$> arbitrary)
                 , eps <$> arbitrary <*> arbitrary
                 , nil <$> arbitrary ]
        r1 = resize (n-1)
        r2 = resize (n `div` 2)
        -- TODO: Check out which extension I need to make this work without the ticks.
        on2 op = r2 $ bimap <$> arbitrary <*> arbitrary <*>  
            (op <$> arb <*> arb)
        on2' op = r2 $ bimap <$> arbitrary <*> arbitrary <*>  
            (op <$> arb <*> arb)
        on2'' op = r2 $ bimap <$> arbitrary <*> arbitrary <*>  
            (op <$> arb <*> arb)
        on1 op = r1 $ bimap <$> arbitrary <*> arbitrary <*> (op <$> arb)
        on1' op = r1 $ bimap <$> arbitrary <*> arbitrary <*> (op <$> arb)
        complex = [ on2 alt, on2' cut, on2'' seq, on1 rep, on1' not ]
    in if n <= 0
    then oneof simple
    else oneof $ simple ++ complex

-- shrink' :: forall f s . REini f s -> [REini f s]
-- shrink' (SymX r) = (SymX <$> shrink r) ++ [EpsX TooMany 'a', NilX TooMany]

instance CoArbitrary SymE
instance (CoArbitrary x, CoArbitrary y) => CoArbitrary (AltI x y)
instance (CoArbitrary x, CoArbitrary y) => CoArbitrary (CutI x y)
instance (CoArbitrary x, CoArbitrary y) => CoArbitrary (SeqI x y)
instance (CoArbitrary x) => CoArbitrary (RepI x)

shrink' :: forall f s . REini f s -> [REini f s]
shrink' (SymX r) = (SymX <$> shrink r) ++ [EpsX TooMany 'a', NilX TooMany]
shrink' (AltX x y) =
    (AltX <$> shrink' x <*> shrink' y)
    ++ (AltX x <$> shrink' y)
    ++ (AltX <$> shrink' x <*> pure y)
shrink' (CutX x y) =
    (CutX <$> shrink' x <*> shrink' y)
    ++ (CutX x <$> shrink' y)
    ++ (CutX <$> shrink' x <*> pure y)
shrink' (SeqX x y) =
    (SeqX <$> shrink' x <*> shrink' y)
    ++ (SeqX x <$> shrink' y)
    ++ (SeqX <$> shrink' x <*> pure y)
shrink' (RepX x) =
    Bimap (Seq (Rep [])) (Rep . (:[])) x
    : (RepX <$> shrink' x)
shrink' (NotX x) =
    NotX <$> shrink' x
shrink' (EpsX f s) = [NilX f]
shrink' (NilX f) = []
shrink' (Bimap f s x) = Bimap f s <$> shrink' x

data Shield r = forall f s . Shield { unShield :: r f s }
instance Show (Shield REini) where
    show (Shield r) = show r

toShield :: Rf -> Shield REini
toShield (Sym' r) = Shield (SymX r)
toShield (Alt' x y) = altS (toShield x) (toShield y)
toShield (Cut' x y) = cutS (toShield x) (toShield y)
toShield (Seq' x y) = seqS (toShield x) (toShield y)
toShield (Rep' x) = repS (toShield x)
toShield (Not' x) = notS (toShield x)
toShield Eps' = Shield eps_
toShield Nil' = Shield nil_
toShield (Uni' l) = uniS (map toShield l)
toShield (Bimap' x) = bimapS (toShield x)

out :: Bifunctor r => Shield r -> r () ()
out (Shield r) = bimap (const ()) (const ()) r

altS, cutS :: RE r => Shield r -> Shield r -> Shield r
altS (Shield x) (Shield y) = Shield (alt x y)
cutS (Shield x) (Shield y) = Shield (cut x y)
seqS (Shield x) (Shield y) = Shield (seq x y)

repS (Shield x) = Shield (rep x)
notS (Shield x) = Shield (not x)

-- need's a `trust me'
uniS :: [Shield REini] -> Shield REini
uniS = Shield . uni . (map $ \(Shield x) -> blunt x)
bimapS (Shield x) = Shield (bimap id id x)

shrink2 op (Shield x) (Shield y)
    = Shield nil_ : Shield eps_ : Shield x : Shield y
    : (if (rf . forget) (run x) > (rf . forget) (run y) then [op (Shield y) (Shield x)] else [])
    ++ tail (op <$> shrinkS' (Shield x) <*> shrinkS' (Shield y))
shrink1 op (Shield x)
    = Shield nil_ : Shield eps_
    : Shield x
    : (op <$> shrinkS (Shield x))

shrinkS' :: Shield REini -> [Shield REini]
shrinkS' x = x : shrinkS x

shrinkS :: Shield REini -> [Shield REini]
shrinkS (Shield (SymX r))
    = Shield nil_
    : Shield eps_
    : (Shield . SymX <$> shrink r)
shrinkS (Shield (AltX x y))
    = shrink2 altS (Shield x) (Shield y)
shrinkS (Shield (CutX x y))
    = shrink2 cutS (Shield x) (Shield y)
shrinkS (Shield (SeqX x y))
    = shrink2 seqS (Shield x) (Shield y)
shrinkS (Shield (RepX x))
    = shrink1 repS (Shield x)
shrinkS (Shield (NotX x))
    = shrink1 notS (Shield x)
shrinkS (Shield (EpsX f s))
    = [Shield $ NilX f]
shrinkS (Shield (NilX f))
    = []
shrinkS (Shield (Bimap f s x))
    = Shield nil_ : Shield eps_ : Shield x : shrinkS (Shield x)
shrinkS (Shield (UniX l))
    = Shield nil_ : Shield eps_ : 
      map uniS (filter (P.not . null) (shrink $ map Shield l))

-- t :: [Shield x] -> Shield x
