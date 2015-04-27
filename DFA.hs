{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Main where

import Test.QuickCheck
import Prelude hiding (even, odd, seq)
import qualified Prelude as P
import Control.Applicative
import qualified Data.Set as Set
import Data.Set(Set)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Red as R hiding (next, Set, main, n)

-- The (->) can actually hide a lot of state.
data DFA a x = DFA { accepts :: x, next :: a -> DFA a x }

even, odd :: DFA a Bool
even = DFA True (const odd)
odd = DFA False (const even)

run :: DFA a x -> [a] -> x
run dfa = accepts . foldl next dfa

prop_even :: String -> Property
prop_even s = P.even (length s) === run even s


prop_odd :: String -> Property
prop_odd s = P.odd (length s) === run odd s

prop_div :: Positive Int -> NonNegative Int -> Property
prop_div (Positive b) (NonNegative n) = run (divN b) (map (read . return) . show $ n) === (n `mod` b == 0)

-- Example of hiding state in the (->)
divN :: Int -> DFA Int Bool
divN n = div 0 where
    div x = DFA (x == 0) (\y -> div $ (x * 10 + y) `mod` n)

-- OK, we can create a D(F)A by hand.  How about some operations on them?
notD :: DFA a Bool -> DFA a Bool
notD (DFA accepts next) = DFA (not accepts) (fmap notD next)

prop_oddEven :: String -> Property
prop_oddEven s = run even s === run (notD odd) s

together :: DFA a (x->y) -> DFA a x -> DFA a y
together (DFA fx f) (DFA x g) = DFA (fx x) (together <$> f <*> g)

instance Functor (DFA a) where
    fmap f (DFA x n) = DFA (f x) (fmap f . n)

instance Applicative (DFA a) where
    (<*>) = together
    pure x = let dfa = DFA x (pure dfa) in dfa

orD :: DFA a Bool -> DFA a Bool -> DFA a Bool
orD = liftA2 (||)

-- This is correct, but blows up.  We fork at each step, but never consolidate.
seq :: DFA a Bool -> DFA a Bool -> DFA a Bool
seq (DFA acc fl) r = orD (fmap (acc &&) r) (DFA False $ \a -> seq (fl a) r)

-- Let's try again with some ID.

-- Non value bearing.
data DfA a id = DfA { start :: Set id
                    , n :: Set id -> Set id
                    , accepting :: Set id -> Bool
                    -- Same semantics as in Red.hs:
                    -- Nothing ~ .
                    -- Just charRange  ~ [charRange]
                    , step :: Map id (Maybe [a])
                    }

-- NOTE: This type signature doesn't promise that n, accepting and step will stay the same.
stepIt :: forall i a . (Ord i, Ord a) => DfA a i -> [a] -> Bool
stepIt (DfA start n accepting step) = accepting . foldl helper start where
    helper :: Set i -> a -> Set i
    helper z char = n $ Set.filter pred z where
        -- drop state by default.
        pred id = maybe True (elem char) $ Map.findWithDefault (Just []) id step

-- data ID = L | R deriving (Eq, Ord, Show, Read)
type ID = Int
compile' :: (Eq a) => Re a x -> DfA a [ID]
compile' (Eps _) = DfA (Set.singleton []) id (Set.member []) (Map.fromList [([], Just [])])
compile' Nil = DfA Set.empty id (const False) Map.empty

compile :: (Eq a) => Re a x -> DfA a [ID]
compile = ($ []) . fold
    symD --  (Maybe [a] -> b) -- Sym
    altD -- -> (b -> b -> b) -- Alt
    _ -- -> (b -> b -> b) -- Cut
    _ -- -> (b -> b -> b) -- Seq
    _ -- -> (b -> b) -- Rep
    notD -- -> (b -> b) -- Not
    epsD
    nilD    _ -- -> (b -> b) -- FMap
    where
    symD l pre = DfA { start = Set.singleton (1:pre)
                     , n = bind f
                     , accepting = Set.member (2:pre)
                     , step = Map.singleton (1:pre) l }
      where
       f [1] = Set.singleton [2]
       f _ = Set.empty

    epsD pre = DfA (Set.singleton pre) (const $ Set.empty) (Set.member pre) Map.empty
    notD (DfA start n accepting step) = DfA start n (not . accepting) step
    nilD = DfA Set.empty id (const False) Map.empty

    altD l r pre = altD' (l $ 0:pre) (r $ 1:pre)
    altD' :: DfA a [ID] -> DfA a [ID] -> DfA a [ID]
    altD' (DfA lStart lN lAccepting lStep)
          (DfA rStart rN rAccepting rStep) = undefined
        -- TODO: hah, we need to separate the states to feed them
        -- to the two old accepting functions.
--        DfA (Set.union lStart rStart) (lN, rN


bind :: (Ord a, Ord b) => (a -> Set b) -> Set a -> Set b
bind f = Set.foldr (Set.union . f) Set.empty


return []
main = $quickCheckAll
