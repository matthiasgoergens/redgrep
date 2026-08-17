-- | Criterion benchmarks (see DESIGN.md).  Engines: the new core (naive and
-- memoised), regex-applicative (Glushkov threads), regex-tdfa (tagged DFA),
-- and the 2016 engines on small inputs.  Save runs under logs/<date>/bench/.
module Main (main) where

import Control.Applicative (optional)
import Criterion.Main
import Data.Either (isRight)
import Data.Maybe (fromJust, isJust)
import qualified Text.Regex.Applicative as RA
import Text.Regex.TDFA ((=~))

import qualified Data.ByteString.Char8 as BC
import qualified Redgrep.Core as C
import qualified Redgrep.Plan as P

-- 2016 engines (small inputs only; both are super-linear).
import qualified DDup
import qualified Final as F
import qualified Red

-- ---------------------------------------------------------------------------
-- Patterns

astarC :: C.RE
astarC = C.rep_ (C.chr 'a')

raAstar :: String -> Bool
raAstar = isJust . RA.match (RA.many (RA.sym 'a'))

tdfaAstar :: String -> Bool
tdfaAstar s = s =~ ("^a*$" :: String)

pingC :: C.RE
pingC = C.seqL [C.rep_ C.dot, C.str "ping", C.rep_ C.dot]

raPing :: String -> Bool
raPing = isJust . RA.match (RA.many RA.anySym *> RA.string "ping" <* RA.many RA.anySym)

tdfaPing :: String -> Bool
tdfaPing s = s =~ ("ping" :: String)

-- (.* ping .*) ∩ ¬(.* flapping .*): the extended-algebra showcase.
flappingC :: C.RE
flappingC =
    C.cut2
        (C.seqL [C.rep_ C.dot, C.str "ping", C.rep_ C.dot])
        (C.not_ (C.seqL [C.rep_ C.dot, C.str "flapping", C.rep_ C.dot]))

ddupFlapping :: String -> Bool
ddupFlapping s = isRight (DDup.dd s re)
  where
    re =
        F.cut
            (i `F.seq` F.string "ping")
            (F.not (i `F.seq` F.string "flapping"))
            `F.seq` i
    i = F.rep (F.sym Nothing)

-- (a?)^n a^n on a^n: the classic backtracking killer.
evilC :: Int -> C.RE
evilC n = C.seqL (replicate n (C.opt (C.chr 'a')) ++ replicate n (C.chr 'a'))

raEvil :: Int -> String -> Bool
raEvil n =
    isJust
        . RA.match
            (foldr (*>) (RA.string (replicate n 'a')) (replicate n (optional (RA.sym 'a'))))

tdfaEvil :: Int -> String -> Bool
tdfaEvil n s = s =~ pat
  where
    pat = "^" ++ concat (replicate n "a?") ++ replicate n 'a' ++ "$" :: String

pingPlan, flappingPlan :: P.Plan
pingPlan = case P.plan 2000 pingC of
    Just p -> p
    Nothing -> error "pingPlan: cap"
flappingPlan = case P.plan 2000 flappingC of
    Just p -> p
    Nothing -> error "flappingPlan: cap"

-- Compiled once, reused across all inputs (the persistent-matcher story).
pingCompiled, flappingCompiled, astarCompiled, div7Compiled :: C.Compiled
pingCompiled = fromJust (C.compile 2000 pingC)
flappingCompiled = fromJust (C.compile 2000 flappingC)
astarCompiled = fromJust (C.compile 2000 astarC)
div7Compiled = fromJust (C.compile 2000 (C.divisibleBy 7))

-- ---------------------------------------------------------------------------

aInput :: Int -> String
aInput n = replicate n 'a'

pingInput :: Int -> String
pingInput n = replicate n 'e' ++ " ping " ++ replicate n 'e'

main :: IO ()
main =
    defaultMain
        [ bgroup
            "astar"
            [ bgroup
                (show n)
                [ bench "core" $ nf (C.match astarC) inp
                , bench "core-memo" $ nf (C.matchMemo astarC) inp
                , bench "core-dfa" $ nf (C.matchDfa astarC) inp
                , bench "core-compiled" $ nf (C.matchCompiled astarCompiled) inp
                , bench "regex-applicative" $ nf raAstar inp
                , bench "regex-tdfa" $ nf tdfaAstar inp
                ]
            | n <- [1000, 10000, 100000]
            , let inp = aInput n
            ]
        , bgroup
            "ping-search"
            [ bgroup
                (show n)
                [ bench "core" $ nf (C.match pingC) inp
                , bench "core-memo" $ nf (C.matchMemo pingC) inp
                , bench "core-dfa" $ nf (C.matchDfa pingC) inp
                , bench "core-compiled" $ nf (C.matchCompiled pingCompiled) inp
                , bench "core-planned" $ nf (P.runPlanBS pingPlan) inpBS
                , bench "regex-applicative" $ nf raPing inp
                , bench "regex-tdfa" $ nf tdfaPing inp
                ]
            | n <- [1000, 10000, 100000]
            , let inp = pingInput n
            , let inpBS = BC.pack inp
            ]
        , bgroup
            "flapping"
            ( [ bgroup
                  (show n)
                  [ bench "core" $ nf (C.match flappingC) inp
                  , bench "core-memo" $ nf (C.matchMemo flappingC) inp
                  , bench "core-dfa" $ nf (C.matchDfa flappingC) inp
                  , bench "core-compiled" $ nf (C.matchCompiled flappingCompiled) inp
                  , bench "core-planned" $ nf (P.runPlanBS flappingPlan) (BC.pack inp)
                  ]
              | n <- [1000, 10000, 100000]
              , let inp = pingInput n
              ]
                ++ [ bgroup
                       (show n ++ "-nohit")
                       [ bench "core-compiled" $ nf (C.matchCompiled flappingCompiled) inp
                       , bench "core-planned" $ nf (P.runPlanBS flappingPlan) (BC.pack inp)
                       ]
                   | n <- [100000]
                   , let inp = replicate n 'e'
                   ]
                ++ [ bgroup
                       (show n ++ "-2016")
                       [ bench "red2016" $ nf (Red.match Red.flapping) inp
                       , bench "ddup2016" $ nf ddupFlapping inp
                       ]
                   | n <- [50, 200]
                   , let inp = pingInput n
                   ]
            )
        , bgroup
            "div7"
            [ bgroup
                (show n)
                [ bench "core" $ nf (C.match (C.divisibleBy 7)) inp
                , bench "core-memo" $ nf (C.matchMemo (C.divisibleBy 7)) inp
                , bench "core-dfa" $ nf (C.matchDfa (C.divisibleBy 7)) inp
                , bench "core-compiled" $ nf (C.matchCompiled div7Compiled) inp
                , bench "core-dfa-3x5x7" $
                    nf (C.matchDfa (C.cutL [C.divisibleBy 3, C.divisibleBy 5, C.divisibleBy 7])) inp
                ]
            | n <- [1000, 10000, 100000]
            , let inp = take n (cycle "0123456789")
            ]
        , bgroup
            "many-short-strings"
            [ bgroup
                (show k)
                [ bench "core-dfa-per-call" $ nf (map (C.matchDfa pingC)) inps
                , bench "core-compiled" $ nf (map (C.matchCompiled pingCompiled)) inps
                , bench "regex-tdfa" $ nf (map tdfaPing) inps
                ]
            | k <- [2000]
            , let inps = [take 20 (drop i (cycle "abc ping xyz pin g")) | i <- [0 .. k]]
            ]
        , bgroup
            "evil-aqn-an"
            [ bgroup
                (show n)
                [ bench "core" $ nf (C.match (evilC n)) inp
                , bench "core-memo" $ nf (C.matchMemo (evilC n)) inp
                , bench "core-dfa" $ nf (C.matchDfa (evilC n)) inp
                , bench "regex-applicative" $ nf (raEvil n) inp
                , bench "regex-tdfa" $ nf (tdfaEvil n) inp
                ]
            | n <- [15, 25]
            , let inp = aInput n
            ]
        ]
