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
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit (exitFailure)
import Test.QuickCheck

import qualified Redgrep.Core as C
import qualified Redgrep.Oracle as O
import qualified Redgrep.Plan as P

-- 2016 engines, kept as differential references until parity (DESIGN.md).
import qualified ArbitraryFinal as AF
import qualified DDup
import qualified Final as F
import qualified Red

-- Three letters, not two: with only {a,b}, character-class canonicalisation
-- (e.g. [ab]∪[bc] vs [abc]) is structurally untestable (design review 2.2).
alphabet :: String
alphabet = "abc"

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

-- Exhaustive length 4 over three letters: 121 strings, comparable coverage
-- budget to the previous 63 over two letters, plus class-merge visibility.
forAllStrings :: Int -> (String -> Bool) -> Property
forAllStrings k p =
    conjoin [counterexample (show s) (p s) | s <- allStrings k]

-- The main theorem: the engine agrees with the oracle.
prop_match_vs_oracle :: SmallRE -> Property
prop_match_vs_oracle (SmallRE r) =
    forAllStrings 4 $ \s -> C.match r s == O.member r s

prop_memo_agrees :: SmallRE -> Property
prop_memo_agrees (SmallRE r) =
    forAllStrings 4 $ \s -> C.matchMemo r s == C.match r s

prop_dfa_agrees :: SmallRE -> Property
prop_dfa_agrees (SmallRE r) =
    forAllStrings 4 $ \s -> C.matchDfa r s == C.match r s

-- Derivative classes: deriv must be constant on each class (soundness of
-- the partition the compiled DFA is built over).
prop_classes_sound :: SmallRE -> Property
prop_classes_sound (SmallRE r) =
    conjoin
        [ counterexample (show c) $
            C.deriv c r == C.deriv (C.repChar (classOf c)) r
        | c <- "abcz"
        ]
  where
    classOf c = head [cls | cls <- C.classes r, C.inCls c cls]

prop_compiled_agrees :: SmallRE -> Property
prop_compiled_agrees (SmallRE r) = case C.compile 500 r of
    Nothing -> label "state cap hit" True
    Just comp ->
        forAllStrings 4 $ \s -> C.matchCompiled comp s == C.match r s

prop_nullable :: SmallRE -> Bool
prop_nullable (SmallRE r) = C.nullable r == O.member r ""

-- The derivative really is the left quotient by one character.
prop_deriv_is_quotient :: SmallRE -> Property
prop_deriv_is_quotient (SmallRE r) =
    forAll (elements alphabet) $ \c ->
        forAllStrings 3 $ \s -> O.member (C.deriv c r) s == O.member r (c : s)

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
    forAllStrings 4 $ \s -> C.match (C.rev r) s == C.match r (reverse s)

prop_rev_involution :: SmallRE -> Property
prop_rev_involution (SmallRE r) =
    forAllStrings 4 $ \s -> C.match (C.rev (C.rev r)) s == C.match r s

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
-- Kleene-algebra / De Morgan law suite (semantic, oracle-arbitrated where
-- cheap, engine-vs-engine otherwise).  Adopted from design review: the smart
-- constructors are the crux of phase 1, and three ad hoc laws undersample
-- them.

semEq :: C.RE -> C.RE -> Property
semEq x y = forAllStrings 4 $ \s -> C.match x s == C.match y s

prop_star_unfold :: SmallRE -> Property
prop_star_unfold (SmallRE x) =
    semEq (C.rep_ x) (C.alt2 C.Eps (C.seq2 x (C.rep_ x)))

prop_seq_distributes_alt :: SmallRE -> SmallRE -> SmallRE -> Property
prop_seq_distributes_alt (SmallRE x) (SmallRE y) (SmallRE z) =
    semEq (C.seq2 x (C.alt2 y z)) (C.alt2 (C.seq2 x y) (C.seq2 x z))

prop_de_morgan :: SmallRE -> SmallRE -> Property
prop_de_morgan (SmallRE x) (SmallRE y) =
    semEq (C.not_ (C.alt2 x y)) (C.cut2 (C.not_ x) (C.not_ y))
        .&&. semEq (C.not_ (C.cut2 x y)) (C.alt2 (C.not_ x) (C.not_ y))

prop_alt_absorbs_cut :: SmallRE -> SmallRE -> Property
prop_alt_absorbs_cut (SmallRE x) (SmallRE y) =
    semEq (C.alt2 x (C.cut2 x y)) x .&&. semEq (C.cut2 x (C.alt2 x y)) x

prop_seq_assoc :: SmallRE -> SmallRE -> SmallRE -> Property
prop_seq_assoc (SmallRE x) (SmallRE y) (SmallRE z) =
    C.seq2 x (C.seq2 y z) === C.seq2 (C.seq2 x y) z

-- ---------------------------------------------------------------------------
-- State-space boundedness: the one measurement that would have caught the
-- 2016 failure mode.  Explore the derivative closure over a probe alphabet
-- ('z' probes the complement side of Neg classes); it must stay finite and
-- small.  The cap is generous — a failure here is a genuine blowup, not
-- noise.  Distribution is collected so drift shows up in the test output.

reachableStates :: String -> Int -> C.RE -> Maybe Int
reachableStates probe cap r0 = go (Set.singleton r0) [r0]
  where
    go seen [] = Just (Set.size seen)
    go seen (r : frontier)
        | Set.size seen > cap = Nothing
        | otherwise =
            let next = [r' | c <- probe, let r' = C.deriv c r, not (r' `Set.member` seen)]
                seen' = foldr Set.insert seen next
            in go seen' (Set.toList (Set.fromList next) ++ frontier)

prop_state_space_bounded :: SmallRE -> Property
prop_state_space_bounded (SmallRE r) = case reachableStates "abcz" 300 r of
    Nothing -> counterexample ("state blowup: >300 states for " ++ show r) False
    Just k -> collect (bucket k) True
  where
    bucket k = show (10 * (k `div` 10)) ++ "-" ++ show (10 * (k `div` 10) + 9) ++ " states"

-- ---------------------------------------------------------------------------
-- Planner rule 1: .* lit .* is substring containment.

prop_plan_contains :: Property
prop_plan_contains = withMaxSuccess 400 $
    forAll litGen $ \lit ->
        forAll (resize 12 (listOf (elements "abc"))) $ \s ->
            let r = C.seqL [C.rep_ C.dot, C.str lit, C.rep_ C.dot]
            in case P.plan 500 r of
                Just p@(P.Contains _) ->
                    P.runPlan p s == C.match r s
                        && P.runPlan p s == (lit `isInfixOf` s)
                _ -> False
  where
    litGen = do
        n <- choose (1, 4)
        vectorOf n (elements "abc")

-- Any plan whatsoever must agree with the engine.
prop_plan_agrees :: SmallRE -> Property
prop_plan_agrees (SmallRE r) = case P.plan 500 r of
    Nothing -> label "state cap hit" True
    Just p -> forAllStrings 4 $ \s -> P.runPlan p s == C.match r s

-- ---------------------------------------------------------------------------
-- Targeted regression family (design review 2.1): "(a|b)* a (a|b)^k" — the
-- kth-from-last-character language, whose minimal DFA has 2^(k+1) states and
-- whose distinguishing strings are longer than the exhaustive sweep above
-- can reach.  Checked against its direct specification, at string lengths
-- up to 2(k+1)+2.

kthFromLast :: Int -> C.RE
kthFromLast k = C.seqL ([C.rep_ ab, C.chr 'a'] ++ replicate k ab)
  where
    ab = C.sym (C.Pos (Set.fromList "ab"))

prop_kth_from_last :: Property
prop_kth_from_last = withMaxSuccess 300 $
    forAll (choose (1, 8)) $ \k ->
        forAll (choose (0, 2 * (k + 1) + 2)) $ \len ->
            forAll (vectorOf len (elements "ab")) $ \s ->
                C.match (kthFromLast k) s
                    == (length s >= k + 1 && s !! (length s - (k + 1)) == 'a')

-- ---------------------------------------------------------------------------
-- Machine nodes: Div7 without the state elimination
-- (github.com/matthiasgoergens/Div7 obtains a multi-kilobyte regex for this
-- language by eliminating states from the same 7-state automaton).  Checked
-- against direct arithmetic, composed with the syntactic algebra, and
-- reversed through the powerset construction.

digitString :: Gen String
digitString = do
    len <- choose (0, 7)
    vectorOf len (elements "0123456789")

prop_divisibility :: Property
prop_divisibility = withMaxSuccess 400 $
    forAll (elements [2, 3, 7, 10]) $ \k ->
        forAll digitString $ \s ->
            C.match (C.divisibleBy k) s
                == (not (null s) && (read s :: Integer) `mod` fromIntegral k == 0)

prop_machine_composes :: Property
prop_machine_composes = withMaxSuccess 400 $
    forAll digitString $ \s ->
        C.match (C.cut2 (C.divisibleBy 7) contains42) s
            == (not (null s)
                    && (read s :: Integer) `mod` 7 == 0
                    && "42" `isInfixOf` s)
  where
    contains42 = C.seqL [C.rep_ C.dot, C.str "42", C.rep_ C.dot]

prop_machine_rev :: Property
prop_machine_rev = withMaxSuccess 400 $
    forAll digitString $ \s ->
        C.match (C.rev (C.divisibleBy 7)) s == C.match (C.divisibleBy 7) (reverse s)

prop_machine_quotient :: Property
prop_machine_quotient = withMaxSuccess 400 $
    forAll digitString $ \u ->
        forAll digitString $ \s ->
            C.match (C.quotient u (C.divisibleBy 7)) s
                == C.match (C.divisibleBy 7) (u ++ s)

-- Nothing magic about 7: intersection of divisibility machines is
-- divisibility by the lcm (here coprime, so the product), built lazily by
-- the derivative engine.
prop_machine_product :: Property
prop_machine_product = withMaxSuccess 400 $
    forAll digitString $ \s ->
        C.match (C.cut2 (C.divisibleBy 3) (C.divisibleBy 5)) s
            == C.match (C.divisibleBy 15) s

prop_compiled_div :: Property
prop_compiled_div = withMaxSuccess 400 $
    case C.compile 100 (C.cut2 (C.divisibleBy 3) (C.divisibleBy 5)) of
        Nothing -> property False
        Just comp ->
            forAll digitString $ \s ->
                C.matchCompiled comp s == C.match (C.divisibleBy 15) s

prop_machine_product_dfa :: Property
prop_machine_product_dfa = withMaxSuccess 400 $
    forAll digitString $ \s ->
        C.matchDfa (C.cut2 (C.divisibleBy 3) (C.divisibleBy 5)) s
            == C.match (C.divisibleBy 15) s

-- The whole point: the derivative closure of divisibleBy 7 is the automaton
-- itself (start, 7 residues, Nil), not a syntactic explosion.
prop_machine_states :: Property
prop_machine_states =
    property $ case reachableStates "0123456789z" 50 (C.divisibleBy 7) of
        Just k -> k <= 12
        Nothing -> False

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
    C.Machine _ _ -> error "toRf: Machine not expressible in 2016 engines"
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
    C.Machine _ _ -> error "toRed: Machine not expressible in 2016 engines"
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
