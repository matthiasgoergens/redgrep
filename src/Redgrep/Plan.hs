-- | The first slice of the phase-4 query planner (DESIGN.md): recognise
-- patterns whose match semantics collapse to a cheaper algorithm and
-- dispatch accordingly.  Rule 1: a full match against @.* lit .*@ is
-- substring containment, and bytestring's 'BC.isInfixOf' (breakSubstring,
-- memchr-backed) beats running any automaton over every character.
--
-- The analysis is structural over the canonical form, so it is sound by
-- construction: it only fires on terms literally shaped
-- @Seq [dot*, c1, .., ck, dot*]@.  Everything else compiles to the DFA.
module Redgrep.Plan
    ( Plan(..)
    , plan
    , runPlan
    , runPlanBS
    , containsShape
    ) where

import qualified Data.ByteString.Char8 as BC
import qualified Data.Set as Set

import Redgrep.Core

data Plan
    = Contains BC.ByteString
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

-- | Plan a regex: literal-containment rule first, DFA fallback (with the
-- given state cap; 'Nothing' if compilation exceeds it).
plan :: Int -> RE -> Maybe Plan
plan cap r = case containsShape r of
    Just lit -> Just (Contains (BC.pack lit))
    Nothing -> Automaton <$> compile cap r

runPlan :: Plan -> String -> Bool
runPlan p s = runPlanBS p (BC.pack s)

runPlanBS :: Plan -> BC.ByteString -> Bool
runPlanBS (Contains lit) s = lit `BC.isInfixOf` s
runPlanBS (Automaton comp) s = matchCompiled comp (BC.unpack s)
