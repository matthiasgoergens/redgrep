-- | The phase-4 query planner (DESIGN.md): recognise patterns whose match
-- semantics admit a cheaper algorithm and dispatch accordingly.
--
-- Rule 1 ('containsShape'): a full match against @.* lit .*@ IS substring
-- containment; bytestring's 'BC.isInfixOf' (breakSubstring, memchr-backed)
-- beats walking any automaton.
--
-- Rule 2 ('requiredLiteral'): a sound necessary-factor analysis.  If every
-- matching string must contain @lit@, then @lit `isInfixOf` s@ is a valid
-- fast rejection before the automaton runs — grep's common case is the
-- non-matching line.  Soundness by construction per operator: a factor
-- required by any 'Cut' conjunct is required; only factors required by ALL
-- 'Alt' branches survive; 'Rep'/'Not'/'InvHom'/'Machine' contribute nothing;
-- adjacent exactly-literal 'Seq' children concatenate.
--
-- This module is byte-oriented (latin-1 view of bytes); the String engines
-- in "Redgrep.Core" remain the Char-semantics reference.
module Redgrep.Plan
    ( Plan(..)
    , plan
    , runPlan
    , runPlanBS
    , containsShape
    , requiredLiteral
    ) where

import qualified Data.ByteString.Char8 as BC
import Data.List (isInfixOf, maximumBy)
import Data.Maybe (maybeToList)
import Data.Ord (comparing)
import qualified Data.Set as Set

import Redgrep.Core

data Plan
    = Contains BC.ByteString
    | Prefiltered BC.ByteString Compiled
    | Automaton Compiled

-- | @Just lit@ iff the regex is canonically @.* lit .*@ for a nonempty
-- literal.
containsShape :: RE -> Maybe String
containsShape (Seq (h : rest@(_ : _)))
    | h == dots
    , last rest == dots
    , Just lit <- traverse single (init rest)
    , not (null lit) =
        Just lit
  where
    dots = rep_ dot
    single (Sym (Pos s)) | Set.size s == 1 = Just (Set.findMin s)
    single _ = Nothing
containsShape _ = Nothing

-- | Facts computed bottom-up: @fExact@ is @Just l@ only if the language is
-- exactly @{l}@; @fReqs@ are literals contained in every matching string.
data Facts = Facts
    { fExact :: Maybe String
    , fReqs :: [String]
    }

facts :: RE -> Facts
facts re = case re of
    Eps -> Facts (Just "") []
    Nil -> Facts Nothing []  -- empty language: conservatively claim nothing
    Sym (Pos s)
        | Set.size s == 1 ->
            let l = [Set.findMin s] in Facts (Just l) [l]
    Sym _ -> Facts Nothing []
    Seq rs -> seqFacts (map facts rs)
    Alt rs -> altFacts (map facts (Set.toList rs))
    Cut rs -> Facts Nothing (concatMap (fReqs . facts) (Set.toList rs))
    Rep _ -> Facts Nothing []  -- epsilon matches, so nothing is required
    Not _ -> Facts Nothing []
    InvHom _ _ -> Facts Nothing []
    Machine _ _ -> Facts Nothing []

seqFacts :: [Facts] -> Facts
seqFacts fs = Facts ex (runs ++ concatMap fReqs fs)
  where
    ex = foldr (\f acc -> (++) <$> fExact f <*> acc) (Just "") fs
    -- Maximal runs of exactly-literal children concatenate into one
    -- required factor (they appear contiguously in every match).
    runs = filter (not . null) (go fs "")
    go [] acc = [acc]
    go (f : rest) acc = case fExact f of
        Just l -> go rest (acc ++ l)
        Nothing -> acc : go rest ""

altFacts :: [Facts] -> Facts
altFacts [] = Facts Nothing []
altFacts fs@(f0 : rest) = Facts ex common
  where
    ex = case map fExact fs of
        (e@(Just _) : es) | all (== e) es -> e
        _ -> Nothing
    -- A literal is required by the union iff it is required by every
    -- branch; being a substring of a branch's required factor suffices.
    common =
        [ l
        | l <- fReqs f0 ++ maybeToList (fExact f0)
        , all (\f -> any (l `isInfixOf`) (fReqs f ++ maybeToList (fExact f))) rest
        ]

-- | The longest literal that every matching string must contain.
requiredLiteral :: RE -> Maybe String
requiredLiteral r = case filter (not . null) (fReqs (facts r)) of
    [] -> Nothing
    ls -> Just (maximumBy (comparing length) ls)

-- | Plan a regex: containment rule, then prefiltered DFA if a required
-- literal exists, then plain DFA (with the given state cap).
plan :: Int -> RE -> Maybe Plan
plan cap r = case containsShape r of
    Just lit -> Just (Contains (BC.pack lit))
    Nothing -> do
        comp <- compile cap r
        pure $ case requiredLiteral r of
            Just lit -> Prefiltered (BC.pack lit) comp
            Nothing -> Automaton comp

runPlan :: Plan -> String -> Bool
runPlan p s = runPlanBS p (BC.pack s)

runPlanBS :: Plan -> BC.ByteString -> Bool
runPlanBS (Contains lit) s = lit `BC.isInfixOf` s
runPlanBS (Prefiltered lit comp) s =
    lit `BC.isInfixOf` s && matchCompiledBS s comp
runPlanBS (Automaton comp) s = matchCompiledBS s comp
