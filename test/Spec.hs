{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Property tests for the phase-1 core (see DESIGN.md).
--
-- Discipline: for each random regex over the alphabet {a,b}, check against
-- ALL strings up to length 5 (63 of them) rather than random strings, so
-- boundary cases are covered deterministically.  The oracle
-- ('Redgrep.Oracle.member') arbitrates every disagreement.
module Main (main) where

import Control.Monad (replicateM, unless)
import Data.Either (isRight)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit (exitFailure)
import Test.QuickCheck

import qualified Redgrep.Core as C
import qualified Redgrep.Oracle as O

-- 2016 engines, kept as differential references until parity (DESIGN.md).
import qualified ArbitraryFinal as AF
import qualified DDup
import qualified Final as F
import qualified Red

alphabet :: String
alphabet = "ab"

-- | All strings over the alphabet up to the given length.
allStrings :: Int -> [String]
allStrings k = concatMap (\n -> replicateM n alphabet) [0 .. k]

-- | Generator producing only canonical terms (built via smart constructors)
-- over positive classes and dot — the fragment the 2016 engines can also
-- express, so one generator serves every property.
newtype SmallRE = SmallRE C.RE
    deriving (Eq, Show)

instance Arbitrary SmallRE where
    arbitrary = SmallRE <$> sized (gen . min 5)
      where
        leaf = frequency
            [ (3, C.sym . C.Pos . Set.fromList <$> sublistOf alphabet)
            , (1, pure C.dot)
            , (1, pure C.Eps)
            , (1, pure C.Nil)
            ]
        gen n
            | n <= 0 = leaf
            | otherwise = frequency
                [ (2, leaf)
                , (2, C.alt2 <$> sub <*> sub)
                , (1, C.cut2 <$> sub <*> sub)
                , (2, C.seq2 <$> sub <*> sub)
                , (1, C.rep_ <$> gen (n - 1))
                , (1, C.not_ <$> gen (n - 1))
                ]
          where
            sub = gen (n `div` 2)
    shrink (SmallRE r) =
        map SmallRE $
            C.children r
                ++ [C.Eps | r /= C.Eps, r /= C.Nil]
                ++ [C.Nil | r /= C.Nil]

forAllStrings :: Int -> (String -> Bool) -> Property
forAllStrings k p =
    conjoin [counterexample (show s) (p s) | s <- allStrings k]

-- The main theorem: the engine agrees with the oracle.
prop_match_vs_oracle :: SmallRE -> Property
prop_match_vs_oracle (SmallRE r) =
    forAllStrings 5 $ \s -> C.match r s == O.member r s

prop_memo_agrees :: SmallRE -> Property
prop_memo_agrees (SmallRE r) =
    forAllStrings 5 $ \s -> C.matchMemo r s == C.match r s

prop_nullable :: SmallRE -> Bool
prop_nullable (SmallRE r) = C.nullable r == O.member r ""

-- The derivative really is the left quotient by one character.
prop_deriv_is_quotient :: SmallRE -> Property
prop_deriv_is_quotient (SmallRE r) =
    forAll (elements alphabet) $ \c ->
        forAllStrings 4 $ \s -> O.member (C.deriv c r) s == O.member r (c : s)

-- Canonical form: these hold structurally, not just semantically.
prop_alt_commutes :: SmallRE -> SmallRE -> Property
prop_alt_commutes (SmallRE x) (SmallRE y) = C.alt2 x y === C.alt2 y x

prop_alt_idempotent :: SmallRE -> Property
prop_alt_idempotent (SmallRE x) = C.alt2 x x === x

prop_not_involution :: SmallRE -> Property
prop_not_involution (SmallRE x) = C.not_ (C.not_ x) === x

prop_quotient_prefix :: SmallRE -> Property
prop_quotient_prefix (SmallRE r) =
    forAll (elements (allStrings 3)) $ \u ->
        forAllStrings 3 $ \s -> C.match (C.quotient u r) s == C.match r (u ++ s)

prop_right_quotient :: SmallRE -> Property
prop_right_quotient (SmallRE r) =
    forAll (elements (allStrings 3)) $ \u ->
        forAllStrings 3 $ \s ->
            C.match (C.rightQuotient u r) s == C.match r (s ++ u)

prop_rev :: SmallRE -> Property
prop_rev (SmallRE r) =
    forAllStrings 5 $ \s -> C.match (C.rev r) s == C.match r (reverse s)

prop_rev_involution :: SmallRE -> Property
prop_rev_involution (SmallRE r) =
    forAllStrings 5 $ \s -> C.match (C.rev (C.rev r)) s == C.match r s

-- Inverse homomorphism: sample maps exercising expansion, erasure, and
-- swapping; both the engine's derivative rule and the oracle must agree
-- with the defining equation.
prop_invHom :: SmallRE -> Property
prop_invHom (SmallRE r) =
    forAll (elements homs) $ \m ->
        forAllStrings 4 $ \s ->
            let lhs = C.match (C.invHom m r) s
                image = concatMap (C.applyHom m) s
            in lhs == C.match r image && lhs == O.member (C.invHom m r) s
  where
    homs =
        [ Map.fromList [('a', "ab"), ('b', "")]
        , Map.fromList [('a', ""), ('b', "")]
        , Map.fromList [('a', "b"), ('b', "a")]
        , Map.fromList [('a', "aa")]
        ]

-- ---------------------------------------------------------------------------
-- Differential tests against the 2016 engines (translatable fragment only).
-- Disagreements here are findings about the old engines; the oracle above
-- arbitrates which side is wrong.

toRf :: C.RE -> F.Rf
toRf = \case
    C.Sym (C.Pos s) -> F.Sym' (Just (Set.toList s))
    C.Sym (C.Neg s)
        | Set.null s -> F.Sym' Nothing
        | otherwise -> error "toRf: negated class not expressible in 2016 engines"
    C.Alt s -> foldr1 F.Alt' (map toRf (Set.toList s))
    C.Cut s -> foldr1 F.Cut' (map toRf (Set.toList s))
    C.Seq l -> foldr1 F.Seq' (map toRf l)
    C.Rep x -> F.Rep' (toRf x)
    C.Not x -> F.Not' (toRf x)
    C.InvHom _ _ -> error "toRf: InvHom not expressible in 2016 engines"
    C.Eps -> F.Eps'
    C.Nil -> F.Nil'

prop_ddup2016_agrees :: SmallRE -> Property
prop_ddup2016_agrees (SmallRE r) =
    C.size r <= 12 ==> case AF.toShield (toRf r) of
        AF.Shield re ->
            forAllStrings 4 $ \s ->
                isRight (DDup.dd s (F.run re)) == C.match r s

toRed :: C.RE -> Red.Re Char ()
toRed = \case
    C.Sym (C.Pos s) -> unit (Red.Sym (Just (Set.toList s)))
    C.Sym (C.Neg s)
        | Set.null s -> unit (Red.Sym Nothing)
        | otherwise -> error "toRed: negated class not expressible in 2016 engines"
    C.Alt s -> foldr1 (\a b -> unit (Red.Alt a b)) (map toRed (Set.toList s))
    C.Cut s -> foldr1 (\a b -> unit (Red.Cut a b)) (map toRed (Set.toList s))
    C.Seq l -> foldr1 (\a b -> unit (Red.Seq a b)) (map toRed l)
    C.Rep x -> unit (Red.Rep (toRed x))
    C.Not x -> Red.Not (toRed x)
    C.InvHom _ _ -> error "toRed: InvHom not expressible in 2016 engines"
    C.Eps -> Red.Eps ()
    C.Nil -> Red.Nil
  where
    unit :: Red.Re Char x -> Red.Re Char ()
    unit = Red.FMap (const ())

prop_red2016_agrees :: SmallRE -> Property
prop_red2016_agrees (SmallRE r) =
    C.size r <= 10 ==> withMaxSuccess 60 $
        forAllStrings 3 $ \s ->
            Red.match (toRed r) s == C.match r s

-- ---------------------------------------------------------------------------

return []

main :: IO ()
main = do
    ok <- $quickCheckAll
    unless ok exitFailure
