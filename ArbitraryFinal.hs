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
module ArbitraryFinal (ArbWrap (..))  where
import Shrink
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

instance Arbitrary (REini Int Int) where
    arbitrary = arb
    shrink = shrink'
a = ArbWrap

arb :: RE r => Gen (r Int Int)
arb = sized $ \n ->
    let simple = [ bimap <$> arbitrary <*> arbitrary <*> (sym <$> arbitrary)
                 , eps <$> arbitrary <*> arbitrary
                 , nil <$> arbitrary ]
        r1 = resize (n-1)
        r2 = resize (n `div` 2)
        on2 op = r2 $ bimap <$> arbitrary <*> arbitrary <*>  
            (op <$> arb <*> arb)
        on1 op = r1 $ bimap <$> arbitrary <*> arbitrary <*> (op <$> arb)
        complex = [ on2 alt, on2 cut, on2 seq, on1 rep, on1 not ]
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

