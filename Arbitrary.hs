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
module Arbitrary where
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


newtype ArbWrap r f s = ArbWrap (r f s)
instance (
