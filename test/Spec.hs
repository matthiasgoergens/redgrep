{-# LANGUAGE LambdaCase #-}

-- | Property tests for the core (see DESIGN.md), on falsify — the Haskell
-- library built on Hypothesis's internal-shrinking model: generators parse a
-- random choice sequence, shrinking edits the choices and re-runs the
-- generator, so every shrunk counterexample satisfies the generator's
-- invariants by construction (canonical terms stay canonical) and no
-- hand-written shrink function exists to fall out of sync.
--
-- Discipline unchanged from the QuickCheck era: for each random regex,
-- check against ALL strings over {a,b,c} up to length 4 plus a fixed set of
-- alphabet-boundary strings; the oracle ('Redgrep.Oracle.member')
-- arbitrates every disagreement.  The generator deliberately emits
-- non-Latin-1 characters, negated classes, and near-full/exactly-full
-- classes — the distribution blind spot behind all three DeepSeek findings.
module Main (main) where

import Control.Monad (replicateM, unless)
import qualified Data.ByteString.Char8 as BC
import Data.List (isInfixOf)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Test.Falsify.Generator (Gen)
import qualified Test.Falsify.Generator as Gen
import qualified Test.Falsify.Range as Range
import Test.Tasty
import Test.Tasty.Falsify
import Test.Tasty.HUnit

import qualified Redgrep.Core as C
import qualified Redgrep.Oracle as O
import qualified Redgrep.Plan as P

-- ---------------------------------------------------------------------------
-- Alphabets and string sweeps

alphabet :: String
alphabet = "abc"

allStrings :: Int -> [String]
allStrings k = concatMap (\n -> replicateM n alphabet) [0 .. k]

lambda :: Char
lambda = '\955'

boundaryStrings :: [String]
boundaryStrings =
    ["\955", "a\955", "\955a", "\187", "\256", "\955\955", "a\955b"]

allChars :: Set.Set Char
allChars = Set.fromDistinctAscList [minBound .. maxBound]

nearFullSet :: Set.Set Char
nearFullSet = allChars Set.\\ Set.fromList ('a' : [lambda])

-- ---------------------------------------------------------------------------
-- Property helpers

eqP :: (Eq a, Show a) => String -> a -> a -> Property ()
eqP what x y =
    unless (x == y) $
        testFailed (what ++ ": " ++ show x ++ " /= " ++ show y)

-- | Exhaustive sweep including the boundary strings.
sweep :: Int -> (String -> Bool) -> Property ()
sweep k p =
    sequence_
        [ unless (p s) (testFailed ("string: " ++ show s))
        | s <- allStrings k ++ boundaryStrings
        ]

-- | Latin-1-only sweep, for the byte-level walker (byte semantics by design).
sweepLatin :: Int -> (String -> Bool) -> Property ()
sweepLatin k p =
    sequence_
        [ unless (p s) (testFailed ("string: " ++ show s))
        | s <- allStrings k
        ]

-- ---------------------------------------------------------------------------
-- Generators (canonical by construction: smart constructors only)

subsetOf :: String -> Gen (Set.Set Char)
subsetOf cs =
    Set.fromList . concat
        <$> mapM (\c -> (\b -> [c | b]) <$> Gen.bool False) cs

genRE :: Gen C.RE
genRE = go (5 :: Int)
  where
    leaf =
        Gen.frequency
            [ (6, C.sym . C.Pos <$> subsetOf alphabet)
            , (2, pure C.dot)
            , (2, pure C.Eps)
            , (2, pure C.Nil)
            , (1, C.sym . C.Pos . Set.insert lambda <$> subsetOf alphabet)
            , (1, C.sym . C.Neg <$> subsetOf (lambda : alphabet))
            , (1, Gen.elem
                    (C.sym (C.Pos nearFullSet)
                        :| [ C.sym (C.Neg nearFullSet)
                           , C.sym (C.Pos allChars)
                           , C.sym (C.Neg allChars)
                           ]))
            ]
    go n
        | n <= 0 = leaf
        | otherwise =
            Gen.frequency
                [ (2, leaf)
                , (2, C.alt2 <$> sub <*> sub)
                , (1, C.cut2 <$> sub <*> sub)
                , (2, C.seq2 <$> sub <*> sub)
                , (1, C.rep_ <$> go (n - 1))
                , (1, C.not_ <$> go (n - 1))
                ]
      where
        sub = go (n `div` 2)

genChar :: Gen Char
genChar = Gen.elem ('a' :| "bc")

genShortString :: Int -> Gen String
genShortString k =
    Gen.list (Range.between (0, fromIntegral k :: Word)) genChar

-- Long strings over an alphabet that exercises Neg classes and unicode;
-- checked engine-vs-engine (linear each), not against the exponential
-- oracle.
genLongString :: Gen String
genLongString =
    Gen.list
        (Range.between (0, 60 :: Word))
        (Gen.frequency
            [ (8, Gen.elem ('a' :| "bc"))
            , (1, Gen.elem ('z' :| [lambda, '\187']))
            ])

genDigits :: Gen String
genDigits =
    Gen.list (Range.between (0, 7 :: Word)) (Gen.elem ('0' :| "123456789"))

-- ---------------------------------------------------------------------------
-- Engine vs oracle

prop_match_vs_oracle :: Property ()
prop_match_vs_oracle = do
    r <- gen genRE
    sweep 4 $ \s -> C.match r s == O.member r s

prop_memo_agrees :: Property ()
prop_memo_agrees = do
    r <- gen genRE
    sweep 4 $ \s -> C.matchMemo r s == C.match r s

prop_dfa_agrees :: Property ()
prop_dfa_agrees = do
    r <- gen genRE
    sweep 4 $ \s -> C.matchDfa r s == C.match r s

prop_compiled_agrees :: Property ()
prop_compiled_agrees = do
    r <- gen genRE
    case C.compile 500 r of
        Nothing -> label "compile" ["state cap hit"]
        Just comp -> sweep 4 $ \s -> C.matchCompiled comp s == C.match r s

prop_bs_matcher_agrees :: Property ()
prop_bs_matcher_agrees = do
    r <- gen genRE
    case C.compile 500 r of
        Nothing -> label "compile" ["state cap hit"]
        Just comp ->
            sweepLatin 4 $ \s ->
                C.matchCompiledBS (BC.pack s) comp == C.matchCompiled comp s

-- Long-string agreement: every engine against naive `match`, whose
-- algorithm (fold deriv, then nullable) is the one PROVED correct for the
-- core algebra by lean/Correctness.lean (matchRE_correct).  The oracle
-- arbitrates short strings; the proven algorithm arbitrates long ones —
-- length is no longer capped by the oracle's exponential cost.
prop_engines_agree_long :: Property ()
prop_engines_agree_long = do
    r <- gen genRE
    s <- gen genLongString
    let reference = C.match r s
    eqP ("matchDfa on " ++ show s) (C.matchDfa r s) reference
    eqP ("matchMemo on " ++ show s) (C.matchMemo r s) reference
    case C.compile 500 r of
        Nothing -> label "compile" ["state cap hit"]
        Just comp ->
            eqP ("matchCompiled on " ++ show s) (C.matchCompiled comp s) reference
    case P.plan 500 r of
        Nothing -> label "plan" ["state cap hit"]
        Just p -> eqP ("plan on " ++ show s) (P.runPlan p s) reference

-- Oracle spot-check at medium length: one random string per case reaches
-- past the exhaustive sweep without paying the oracle's exponential cost
-- on every string.
prop_oracle_random_medium :: Property ()
prop_oracle_random_medium = do
    r <- gen genRE
    s <- gen (genShortString 7)
    eqP ("oracle on " ++ show s) (C.match r s) (O.member r s)

prop_nullable :: Property ()
prop_nullable = do
    r <- gen genRE
    eqP "nullable" (C.nullable r) (O.member r "")

prop_deriv_is_quotient :: Property ()
prop_deriv_is_quotient = do
    r <- gen genRE
    c <- gen genChar
    sweep 3 $ \s -> O.member (C.deriv c r) s == O.member r (c : s)

prop_classes_sound :: Property ()
prop_classes_sound = do
    r <- gen genRE
    let classOf c = head [cls | cls <- C.classes r, C.inCls c cls]
    sequence_
        [ eqP ("class of " ++ show c)
            (C.deriv c r)
            (C.deriv (C.repChar (classOf c)) r)
        | c <- "abcz" ++ [lambda]
        ]

-- ---------------------------------------------------------------------------
-- Canonical-form and algebraic laws

prop_alt_commutes :: Property ()
prop_alt_commutes = do
    x <- gen genRE
    y <- gen genRE
    eqP "alt comm" (C.alt2 x y) (C.alt2 y x)

prop_alt_idempotent :: Property ()
prop_alt_idempotent = do
    x <- gen genRE
    eqP "alt idem" (C.alt2 x x) x

prop_not_involution :: Property ()
prop_not_involution = do
    x <- gen genRE
    eqP "not/not" (C.not_ (C.not_ x)) x

prop_seq_assoc :: Property ()
prop_seq_assoc = do
    x <- gen genRE
    y <- gen genRE
    z <- gen genRE
    eqP "seq assoc" (C.seq2 x (C.seq2 y z)) (C.seq2 (C.seq2 x y) z)

semEq :: C.RE -> C.RE -> Property ()
semEq x y = sweep 4 $ \s -> C.match x s == C.match y s

prop_star_unfold :: Property ()
prop_star_unfold = do
    x <- gen genRE
    semEq (C.rep_ x) (C.alt2 C.Eps (C.seq2 x (C.rep_ x)))

prop_seq_distributes_alt :: Property ()
prop_seq_distributes_alt = do
    x <- gen genRE
    y <- gen genRE
    z <- gen genRE
    semEq (C.seq2 x (C.alt2 y z)) (C.alt2 (C.seq2 x y) (C.seq2 x z))

prop_de_morgan :: Property ()
prop_de_morgan = do
    x <- gen genRE
    y <- gen genRE
    semEq (C.not_ (C.alt2 x y)) (C.cut2 (C.not_ x) (C.not_ y))
    semEq (C.not_ (C.cut2 x y)) (C.alt2 (C.not_ x) (C.not_ y))

prop_alt_absorbs_cut :: Property ()
prop_alt_absorbs_cut = do
    x <- gen genRE
    y <- gen genRE
    semEq (C.alt2 x (C.cut2 x y)) x
    semEq (C.cut2 x (C.alt2 x y)) x

-- ---------------------------------------------------------------------------
-- Closure operations

prop_quotient_prefix :: Property ()
prop_quotient_prefix = do
    r <- gen genRE
    u <- gen (genShortString 3)
    sweep 3 $ \s -> C.match (C.quotient u r) s == C.match r (u ++ s)

prop_right_quotient :: Property ()
prop_right_quotient = do
    r <- gen genRE
    u <- gen (genShortString 3)
    sweep 3 $ \s -> C.match (C.rightQuotient u r) s == C.match r (s ++ u)

prop_rev :: Property ()
prop_rev = do
    r <- gen genRE
    sweep 4 $ \s -> C.match (C.rev r) s == C.match r (reverse s)

prop_rev_involution :: Property ()
prop_rev_involution = do
    r <- gen genRE
    sweep 4 $ \s -> C.match (C.rev (C.rev r)) s == C.match r s

prop_invHom :: Property ()
prop_invHom = do
    r <- gen genRE
    m <- gen (Gen.elem (NE.fromList homs))
    sweep 4 $ \s ->
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
-- State space and the kth-from-last regression family

reachableStates :: String -> Int -> C.RE -> Maybe Int
reachableStates probe cap r0 = go (Set.singleton r0) [r0]
  where
    go seen [] = Just (Set.size seen)
    go seen (r : frontier)
        | Set.size seen > cap = Nothing
        | otherwise =
            let next =
                    [ r'
                    | c <- probe
                    , let r' = C.deriv c r
                    , not (r' `Set.member` seen)
                    ]
            in go (foldr Set.insert seen next)
                  (Set.toList (Set.fromList next) ++ frontier)

prop_state_space_bounded :: Property ()
prop_state_space_bounded = do
    r <- gen genRE
    case reachableStates ("abcz" ++ [lambda]) 300 r of
        Nothing -> testFailed ("state blowup: >300 states for " ++ show r)
        Just k -> collect "states" [10 * (k `div` 10)]

prop_kth_from_last :: Property ()
prop_kth_from_last = do
    k <- gen (Gen.inRange (Range.between (1, 8 :: Word)))
    let ki = fromIntegral k :: Int
    s <- gen (Gen.list
                (Range.between (0, fromIntegral (2 * (ki + 1) + 2) :: Word))
                (Gen.elem ('a' :| "b")))
    let ab = C.sym (C.Pos (Set.fromList "ab"))
        r = C.seqL ([C.rep_ ab, C.chr 'a'] ++ replicate ki ab)
    eqP ("k=" ++ show ki ++ " s=" ++ show s)
        (C.match r s)
        (length s >= ki + 1 && s !! (length s - (ki + 1)) == 'a')

-- ---------------------------------------------------------------------------
-- Machines

prop_divisibility :: Property ()
prop_divisibility = do
    k <- gen (Gen.elem (2 :| [3, 7, 10]))
    s <- gen genDigits
    eqP ("divisibleBy " ++ show k ++ " on " ++ show s)
        (C.match (C.divisibleBy k) s)
        (not (null s) && (read s :: Integer) `mod` fromIntegral (k :: Int) == 0)

prop_machine_composes :: Property ()
prop_machine_composes = do
    s <- gen genDigits
    let contains42 = C.seqL [C.rep_ C.dot, C.str "42", C.rep_ C.dot]
    eqP ("div7 ∩ contains42 on " ++ show s)
        (C.match (C.cut2 (C.divisibleBy 7) contains42) s)
        (not (null s) && (read s :: Integer) `mod` 7 == 0 && "42" `isInfixOf` s)

prop_machine_rev :: Property ()
prop_machine_rev = do
    s <- gen genDigits
    eqP ("rev div7 on " ++ show s)
        (C.match (C.rev (C.divisibleBy 7)) s)
        (C.match (C.divisibleBy 7) (reverse s))

prop_machine_quotient :: Property ()
prop_machine_quotient = do
    u <- gen genDigits
    s <- gen genDigits
    eqP "div7 quotient"
        (C.match (C.quotient u (C.divisibleBy 7)) s)
        (C.match (C.divisibleBy 7) (u ++ s))

prop_machine_product :: Property ()
prop_machine_product = do
    s <- gen genDigits
    eqP "div3 ∩ div5 ≡ div15"
        (C.match (C.cut2 (C.divisibleBy 3) (C.divisibleBy 5)) s)
        (C.match (C.divisibleBy 15) s)
    eqP "dfa path"
        (C.matchDfa (C.cut2 (C.divisibleBy 3) (C.divisibleBy 5)) s)
        (C.match (C.divisibleBy 15) s)

-- ---------------------------------------------------------------------------
-- Planner

prop_plan_contains :: Property ()
prop_plan_contains = do
    lit <- gen (Gen.list (Range.between (1, 4 :: Word)) genChar)
    s <- gen (genShortString 12)
    let r = C.seqL [C.rep_ C.dot, C.str lit, C.rep_ C.dot]
    case P.plan 500 r of
        Just p@(P.Contains _ _) -> do
            eqP "plan vs engine" (P.runPlan p s) (C.match r s)
            eqP "plan vs isInfixOf" (P.runPlan p s) (lit `isInfixOf` s)
        _ -> testFailed "containment shape not recognised"

prop_plan_agrees :: Property ()
prop_plan_agrees = do
    r <- gen genRE
    case P.plan 500 r of
        Nothing -> label "plan" ["state cap hit"]
        Just p -> sweep 4 $ \s -> P.runPlan p s == C.match r s

prop_required_literal_sound :: Property ()
prop_required_literal_sound = do
    r <- gen genRE
    case P.requiredLiteral r of
        Nothing -> label "literal" ["none"]
        Just lit -> do
            label "literal" ["found"]
            sweep 4 $ \s -> not (C.match r s) || (lit `isInfixOf` s)

-- ---------------------------------------------------------------------------
-- Verbatim regressions (deterministic; tasty-hunit)

unit_flapping_required :: Assertion
unit_flapping_required =
    P.requiredLiteral
        (C.cut2
            (C.seqL [C.rep_ C.dot, C.str "ping", C.rep_ C.dot])
            (C.not_ (C.seqL [C.rep_ C.dot, C.str "flapping", C.rep_ C.dot])))
        @?= Just "ping"

unit_plan_unicode :: Assertion
unit_plan_unicode = do
    let r = C.seqL [C.rep_ C.dot, C.str [lambda], C.rep_ C.dot]
        r2 = C.altL [C.chr lambda, C.chr '\956']
    case (P.plan 500 r, P.plan 500 r2) of
        (Just p, Just p2) -> do
            P.runPlan p "\187" @?= C.match r "\187"
            P.runPlan p2 [lambda] @?= C.match r2 [lambda]
        _ -> assertFailure "plans not built"

unit_neg_full_class :: Assertion
unit_neg_full_class = do
    C.sym (C.Neg allChars) @?= C.Nil
    assertBool "compile survives" $
        case C.compile 10 (C.sym (C.Neg allChars)) of
            Just _ -> True
            Nothing -> False

unit_machine_full_tabulation :: Assertion
unit_machine_full_tabulation = do
    let fsm =
            C.Fsm
                { C.fsmTrans =
                    Map.fromList [((0, c), 0) | c <- [minBound .. maxBound :: Char]]
                , C.fsmElse = Map.empty
                , C.fsmAccept = Set.singleton 0
                }
    assertBool "compile survives full tabulation" $
        case C.compile 1 (C.machineAt fsm 0) of
            Just _ -> True
            Nothing -> False

unit_div7_states :: Assertion
unit_div7_states =
    assertBool "div7 derivative closure small" $
        case reachableStates "0123456789z" 50 (C.divisibleBy 7) of
            Just k -> k <= 12
            Nothing -> False

unit_compiled_div_product :: Assertion
unit_compiled_div_product =
    case C.compile 100 (C.cut2 (C.divisibleBy 3) (C.divisibleBy 5)) of
        Nothing -> assertFailure "product machine exceeded cap"
        Just comp ->
            sequence_
                [ C.matchCompiled comp s @?= C.match (C.divisibleBy 15) s
                | s <- ["", "0", "15", "30", "31", "45", "150", "1234567"]
                ]

-- ---------------------------------------------------------------------------

main :: IO ()
main =
    defaultMain $
        testGroup
            "redgrep"
            [ testGroup
                "engine-vs-oracle"
                [ testProperty "match agrees with oracle" prop_match_vs_oracle
                , testProperty "matchMemo agrees" prop_memo_agrees
                , testProperty "matchDfa agrees" prop_dfa_agrees
                , testProperty "matchCompiled agrees" prop_compiled_agrees
                , testProperty "byte walker agrees (latin-1)" prop_bs_matcher_agrees
                , testProperty "nullable decides empty string" prop_nullable
                , testProperty "derivative is left quotient" prop_deriv_is_quotient
                , testProperty "derivative classes sound" prop_classes_sound
                , testProperty "engines agree on long strings" prop_engines_agree_long
                , testProperty "oracle spot-check, medium length" prop_oracle_random_medium
                ]
            , testGroup
                "laws"
                [ testProperty "alt commutes (structural)" prop_alt_commutes
                , testProperty "alt idempotent (structural)" prop_alt_idempotent
                , testProperty "not involution (structural)" prop_not_involution
                , testProperty "seq associative (structural)" prop_seq_assoc
                , testProperty "star unfold" prop_star_unfold
                , testProperty "seq distributes over alt" prop_seq_distributes_alt
                , testProperty "De Morgan" prop_de_morgan
                , testProperty "absorption" prop_alt_absorbs_cut
                ]
            , testGroup
                "closure-ops"
                [ testProperty "prefix quotient" prop_quotient_prefix
                , testProperty "right quotient" prop_right_quotient
                , testProperty "reversal" prop_rev
                , testProperty "reversal involutive" prop_rev_involution
                , testProperty "inverse homomorphism" prop_invHom
                ]
            , testGroup
                "state-space"
                [ testProperty "derivative closure bounded" prop_state_space_bounded
                , testProperty "kth-from-last family" prop_kth_from_last
                ]
            , testGroup
                "machines"
                [ testProperty "divisibility spec" prop_divisibility
                , testProperty "div7 ∩ contains-42" prop_machine_composes
                , testProperty "machine reversal" prop_machine_rev
                , testProperty "machine quotient" prop_machine_quotient
                , testProperty "div3 ∩ div5 ≡ div15" prop_machine_product
                ]
            , testGroup
                "planner"
                [ testProperty "containment shape" prop_plan_contains
                , testProperty "any plan agrees with engine" prop_plan_agrees
                , testProperty "required literal sound" prop_required_literal_sound
                ]
            , testGroup
                "regressions"
                [ testCase "flapping requires ping" unit_flapping_required
                , testCase "unicode plans (DeepSeek 1)" unit_plan_unicode
                , testCase "Neg-full class (DeepSeek 1)" unit_neg_full_class
                , testCase "full tabulation (DeepSeek 2)" unit_machine_full_tabulation
                , testCase "div7 closure size" unit_div7_states
                , testCase "compiled product machine" unit_compiled_div_product
                ]
            ]
