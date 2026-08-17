{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}

-- | Phase 1 of the rework (see DESIGN.md): the value-free core.
--
-- An untyped, 'Ord'-erable regex AST kept in ACI-canonical form by smart
-- constructors, with Brzozowski derivatives as the engine.  No parse values,
-- no closures: everything here is first-order data, so states compare,
-- deduplicate and memoise.  Evidence comes back in phase 2, at the two ends
-- of the pipeline, never in the middle.
module Redgrep.Core
    ( RE(..)
    , Cls(..)
    , inCls
      -- * Smart constructors (the only way to build canonical terms)
    , sym, chr, dot, top
    , altL, alt2, cutL, cut2, seq2, seqL, rep_, not_, opt
    , str
      -- * Finite state machines as primitives
    , Fsm(..)
    , machineAt
    , stepFsm
    , modBase
    , divisibleBy
      -- * The engine
    , nullable
    , deriv
    , match
    , matchMemo
    , matchDfa
      -- * Derivative classes and compiled matchers
    , classes
    , repChar
    , Compiled
    , compile
    , matchCompiled
    , matchCompiledBS
      -- * Closure operations
    , quotient
    , rightQuotient
    , rev
    , invHom
    , applyHom
      -- * Misc
    , size
    , children
    ) where

import Data.Array.Unboxed (UArray, listArray)
import qualified Data.ByteString as B
import qualified Data.Array.Unboxed as UA
import Data.Char (intToDigit)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.List (foldl', partition)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- | Character classes: a finite set, or the complement of one (@'Neg' empty@
-- is @.@).  Kept normalised so classes compare structurally.
data Cls = Pos (Set Char) | Neg (Set Char)
    deriving (Eq, Ord, Show)

inCls :: Char -> Cls -> Bool
inCls c (Pos s) = Set.member c s
inCls c (Neg s) = not (Set.member c s)

charCount :: Int
charCount = fromEnum (maxBound :: Char) + 1

-- | Total emptiness test: @Neg s@ is empty exactly when s holds every Char
-- (DeepSeek review 2026-08-17: the old @Neg _ -> False@ let a semantically
-- empty class through 'sym', and 'compile' then crashed in 'repChar').
clsEmpty :: Cls -> Bool
clsEmpty (Pos s) = Set.null s
clsEmpty (Neg s) = Set.size s == charCount

clsFull :: Cls -> Bool
clsFull (Pos s) = Set.size s == charCount
clsFull (Neg s) = Set.null s

-- | Canonical representative: the full class is always @Neg empty@ (dot).
normCls :: Cls -> Cls
normCls c
    | clsFull c = Neg Set.empty
    | otherwise = c

clsUnion :: Cls -> Cls -> Cls
clsUnion (Pos a) (Pos b) = Pos (Set.union a b)
clsUnion (Neg a) (Neg b) = Neg (Set.intersection a b)
clsUnion (Pos a) (Neg b) = Neg (b Set.\\ a)
clsUnion a@(Neg _) b@(Pos _) = clsUnion b a

clsIsect :: Cls -> Cls -> Cls
clsIsect (Pos a) (Pos b) = Pos (Set.intersection a b)
clsIsect (Neg a) (Neg b) = Neg (Set.union a b)
clsIsect (Pos a) (Neg b) = Pos (a Set.\\ b)
clsIsect a@(Neg _) b@(Pos _) = clsIsect b a

-- | The core AST.  Invariants (maintained by the smart constructors, relied
-- on by 'Eq'/'Ord' canonicity):
--
--   * 'Alt': at least two elements, no 'Nil', no nested 'Alt', not 'top',
--     at most one 'Sym' (classes merged).
--   * 'Cut': at least two elements, no 'top', no nested 'Cut', no 'Nil',
--     at most one 'Sym'.
--   * 'Seq': at least two elements, no 'Eps'\/'Nil', no nested 'Seq'.
--   * 'Rep': body is not 'Nil'\/'Eps'\/'Rep'\/'top'.
--   * 'Not': body is not 'Not'.
--   * 'Sym': class is nonempty (an empty class is 'Nil').
--
-- 'InvHom' carries the homomorphism as a 'Map' (not a function) precisely so
-- the AST keeps decidable equality and ordering.
data RE
    = Sym Cls
    | Alt (Set RE)
    | Cut (Set RE)
    | Seq [RE]
    | Rep RE
    | Not RE
    | InvHom (Map Char String) RE
    | Machine Fsm Int  -- ^ a DFA and its current state; see 'machineAt'
    | Eps
    | Nil
    deriving (Eq, Ord, Show)

-- | A deterministic finite automaton over 'Int' states, as plain data so
-- 'RE' keeps decidable equality.  Transitions are total by convention:
-- a (state, char) pair absent from 'fsmTrans' falls back to that state's
-- 'fsmElse' entry, and an absent 'fsmElse' entry falls back to the implicit
-- dead state @-1@ (non-accepting, absorbing).  A 'Machine' node's language
-- is the set of strings leading from its current state to an accepting one.
--
-- Rationale (see also matthiasgoergens\/Div7): languages like
-- \"divisible by 7\" have tiny automata but enormous regexes — Div7 obtains
-- one by state elimination and it fills a file.  Under derivatives a machine
-- node is native: the derivative IS the table transition, and the
-- surrounding algebra (Boolean operations, seq, rep, quotients, invHom)
-- composes with it for free.
data Fsm = Fsm
    { fsmTrans :: Map (Int, Char) Int
    , fsmElse :: Map Int Int
    , fsmAccept :: Set Int
    }
    deriving (Eq, Ord, Show)

stepFsm :: Fsm -> Int -> Char -> Int
stepFsm f q c =
    Map.findWithDefault (Map.findWithDefault (-1) q (fsmElse f)) (q, c) (fsmTrans f)

-- | The smart constructor for machine nodes: the dead state is 'Nil'.
machineAt :: Fsm -> Int -> RE
machineAt f q
    | q < 0 = Nil
    | otherwise = Machine f q

-- | @modBase b k r@: nonempty digit strings in base @b@ (2–16, digits
-- @0..b-1@ as characters via 'intToDigit') whose value is congruent to @r@
-- modulo @k@.  Leading zeros are allowed.  State @k@ is the start state
-- (\"no digits read yet\"), states @0..k-1@ are residues.
modBase :: Int -> Int -> Int -> RE
modBase b k r
    | b < 2 || b > 16 = error "modBase: base out of range 2..16"
    | k < 1 || r < 0 || r >= k = error "modBase: bad modulus or residue"
    | otherwise = machineAt fsm k
  where
    fsm =
        Fsm
            { fsmTrans =
                Map.fromList $
                    [((k, intToDigit d), d `mod` k) | d <- [0 .. b - 1]]
                        ++ [ ((q, intToDigit d), (q * b + d) `mod` k)
                           | q <- [0 .. k - 1]
                           , d <- [0 .. b - 1]
                           ]
            , fsmElse = Map.empty
            , fsmAccept = Set.singleton r
            }

-- | Decimal divisibility: @divisibleBy 7@ is Div7 without the state
-- elimination.
divisibleBy :: Int -> RE
divisibleBy k = modBase 10 k 0

-- | @¬∅@: the universal language @Σ*@, the unit of 'cutL'.
top :: RE
top = Not Nil

sym :: Cls -> RE
sym cls
    | clsEmpty cls = Nil
    | otherwise = Sym (normCls cls)

chr :: Char -> RE
chr = sym . Pos . Set.singleton

dot :: RE
dot = Sym (Neg Set.empty)

str :: String -> RE
str = seqL . map chr

isSym :: RE -> Bool
isSym (Sym _) = True
isSym _ = False

-- | n-ary union, flattened, sorted, deduplicated; 'Nil' dropped, 'top'
-- absorbing, 'Sym' members merged into one class.
altL :: [RE] -> RE
altL = post . foldr flat []
  where
    flat (Alt s) acc = Set.toList s ++ acc
    flat Nil acc = acc
    flat r acc = r : acc
    post rs
        | top `elem` rs = top
        | otherwise = case Set.toList set of
            [] -> Nil
            [x] -> x
            _ -> Alt set
      where
        (syms, rest) = partition isSym rs
        merged = case [cls | Sym cls <- syms] of
            [] -> []
            (c : cs) -> case sym (foldl' clsUnion c cs) of
                Nil -> []
                s -> [s]
        set = Set.fromList (merged ++ rest)

alt2 :: RE -> RE -> RE
alt2 x y = altL [x, y]

-- | n-ary intersection, dual to 'altL': 'top' dropped, 'Nil' absorbing,
-- 'Sym' members merged by intersection.  The empty intersection is 'top'.
cutL :: [RE] -> RE
cutL = post . foldr flat []
  where
    flat (Cut s) acc = Set.toList s ++ acc
    flat r acc | r == top = acc
    flat r acc = r : acc
    post rs
        | Nil `elem` rs = Nil
        | otherwise = case merged of
            Just Nil -> Nil
            _ -> case Set.toList set of
                [] -> top
                [x] -> x
                _ -> Cut set
      where
        (syms, rest) = partition isSym rs
        merged = case [cls | Sym cls <- syms] of
            [] -> Nothing
            (c : cs) -> Just (sym (foldl' clsIsect c cs))
        set = Set.fromList (maybe [] pure merged ++ rest)

cut2 :: RE -> RE -> RE
cut2 x y = cutL [x, y]

seq2 :: RE -> RE -> RE
seq2 Nil _ = Nil
seq2 _ Nil = Nil
seq2 Eps y = y
seq2 x Eps = x
seq2 x y = Seq (toL x ++ toL y)
  where
    toL (Seq l) = l
    toL r = [r]

seqL :: [RE] -> RE
seqL = foldr seq2 Eps

rep_ :: RE -> RE
rep_ Nil = Eps
rep_ Eps = Eps
rep_ r@(Rep _) = r
rep_ r | r == top = top
rep_ r = Rep r

not_ :: RE -> RE
not_ (Not r) = r
not_ r = Not r

-- | @r?@
opt :: RE -> RE
opt r = alt2 Eps r

-- | Does the language contain the empty string?
nullable :: RE -> Bool
nullable = \case
    Sym _ -> False
    Alt rs -> any nullable (Set.toList rs)
    Cut rs -> all nullable (Set.toList rs)
    Seq rs -> all nullable rs
    Rep _ -> True
    Not r -> not (nullable r)
    InvHom _ r -> nullable r  -- h "" == ""
    Machine f q -> Set.member q (fsmAccept f)
    Eps -> True
    Nil -> False

-- | Brzozowski derivative.  Commutes with every constructor, including
-- complement; for 'InvHom' the rule is
-- @d_c (h⁻¹ L) = h⁻¹ (d_{h c} L)@ (derive by the image string).
deriv :: Char -> RE -> RE
deriv c = \case
    Sym cls -> if inCls c cls then Eps else Nil
    Alt rs -> altL (map (deriv c) (Set.toList rs))
    Cut rs -> cutL (map (deriv c) (Set.toList rs))
    Seq (r : rs) ->
        let rest = seqL rs
            d1 = seq2 (deriv c r) rest
        in if nullable r then alt2 d1 (deriv c rest) else d1
    Seq [] -> Nil  -- unreachable under the invariants
    Rep r -> seq2 (deriv c r) (rep_ r)
    Not r -> not_ (deriv c r)
    InvHom m r -> invHom m (quotient (applyHom m c) r)
    Machine f q -> machineAt f (stepFsm f q c)
    Eps -> Nil
    Nil -> Nil

-- | Match by re-deriving each step; the honest baseline.
match :: RE -> String -> Bool
match r = nullable . foldl' (flip deriv) r

-- | Match with a per-run transition cache: once a (state, char) pair has
-- been seen, its derivative is looked up rather than recomputed.  The state
-- set is finite (up to the implemented canonical form), so the cache is
-- bounded per regex.  Phase 3 replaces the structural keys with interned
-- state numbers.
matchMemo :: RE -> String -> Bool
matchMemo r0 = go Map.empty r0
  where
    go _ r [] = nullable r
    go cache r (c : cs) = case Map.lookup (r, c) cache of
        Just r' -> go cache r' cs
        Nothing ->
            let r' = deriv c r
            in go (Map.insert (r, c) r' cache) r' cs

-- | Phase-3 step 1: a lazily built, interned DFA.  Each distinct derivative
-- state pays the structural comparison ONCE (on first encounter, to obtain
-- its id); after that, transitions are id-to-id lookups and the regex terms
-- are never compared again.  This is what 'matchMemo' should have been: its
-- structural cache keys made every HIT cost a full term comparison, which
-- machine nodes turned pathological (~1000x on div7, see DESIGN.md).
data Dfa = Dfa
    { dfaIds :: !(Map RE Int)
    , dfaNull :: !(IntMap Bool)
    , dfaTerm :: !(IntMap RE)
    , dfaDelta :: !(IntMap (Map Char Int))
    }

internState :: RE -> Dfa -> (Int, Dfa)
internState r d = case Map.lookup r (dfaIds d) of
    Just i -> (i, d)
    Nothing ->
        ( i
        , d
            { dfaIds = Map.insert r i (dfaIds d)
            , dfaNull = IntMap.insert i (nullable r) (dfaNull d)
            , dfaTerm = IntMap.insert i r (dfaTerm d)
            , dfaDelta = IntMap.insert i Map.empty (dfaDelta d)
            }
        )
  where
    i = Map.size (dfaIds d)

matchDfa :: RE -> String -> Bool
matchDfa r0 s0 =
    let (i0, d0) = internState r0 (Dfa Map.empty IntMap.empty IntMap.empty IntMap.empty)
    in go d0 i0 s0
  where
    go d i [] = dfaNull d IntMap.! i
    go d i (c : cs) = case Map.lookup c (dfaDelta d IntMap.! i) of
        Just j -> go d j cs
        Nothing ->
            let r' = deriv c (dfaTerm d IntMap.! i)
                (j, d') = internState r' d
                d'' = d' {dfaDelta = IntMap.adjust (Map.insert c j) i (dfaDelta d')}
            in go d'' j cs

-- | Left quotient by a string: @quotient u r@ matches @s@ iff @r@ matches
-- @u ++ s@.  This is just an iterated derivative.
quotient :: String -> RE -> RE
quotient u r = foldl' (flip deriv) r u

-- ---------------------------------------------------------------------------
-- Derivative classes (Owens–Reppy–Turon): a finite partition of the whole
-- alphabet such that 'deriv' is constant on each class.  This is what makes
-- an eager, persistent DFA constructible: transitions are enumerated per
-- class, not per character.

complementCls :: Cls -> Cls
complementCls (Pos s) = Neg s
complementCls (Neg s) = Pos s

emptyCls :: Cls -> Bool
emptyCls = clsEmpty

-- | Pairwise refinement of two partitions.  Deduplicated: without this the
-- list length multiplies per refinement step and nested terms explode
-- exponentially in memory (observed: a test run killed at multi-GB).  The
-- distinct classes are bounded by the atoms of the Boolean algebra the leaf
-- classes generate, which is small.
refine :: [Cls] -> [Cls] -> [Cls]
refine xs ys =
    Set.toList . Set.fromList $
        filter (not . emptyCls) [clsIsect x y | x <- xs, y <- ys]

everything :: [Cls]
everything = [Neg Set.empty]

-- | A partition of the alphabet on which @deriv · r@ is constant per class.
classes :: RE -> [Cls]
classes = \case
    Sym c -> filter (not . emptyCls) [c, complementCls c]
    Alt rs -> foldr (refine . classes) everything (Set.toList rs)
    Cut rs -> foldr (refine . classes) everything (Set.toList rs)
    Seq (r : rs)
        | nullable r -> refine (classes r) (classes (seqL rs))
        | otherwise -> classes r
    Seq [] -> everything
    Rep r -> classes r
    Not r -> classes r
    -- Domain characters behave individually (their images differ); identity
    -- characters behave like the underlying regex, so refine against it.
    InvHom m r ->
        refine
            ([Pos (Set.singleton c) | c <- Map.keys m] ++ [Neg (Map.keysSet m)])
            (classes r)
    -- Tabulated characters grouped by target state; everything else follows
    -- the else-transition.
    Machine f q ->
        let byTarget =
                Map.fromListWith
                    Set.union
                    [(t, Set.singleton c) | ((q', c), t) <- Map.toList (fsmTrans f), q' == q]
            tabulated = Set.unions (Map.elems byTarget)
        in [Pos s | s <- Map.elems byTarget] ++ [Neg tabulated]
    Eps -> everything
    Nil -> everything

-- | A representative character of a nonempty class.
repChar :: Cls -> Char
repChar (Pos s) = Set.findMin s
repChar (Neg s) = head [c | c <- [minBound ..], not (Set.member c s)]

-- | An eagerly built DFA over derivative classes: persistent, reusable
-- across calls, with all interning cost paid at compile time.  Returns
-- 'Nothing' if more than the given number of states are reachable
-- (intersection can be genuinely exponential; see DESIGN.md).
data Compiled = Compiled
    { compNull :: !(IntMap Bool)
    , compTrans :: !(IntMap [(Cls, Int)])  -- authoritative; used above ASCII
    , compDense :: !(IntMap (UArray Int Int))  -- chars 0..255, precomputed
    , compStart :: !Int
    }

compile :: Int -> RE -> Maybe Compiled
compile cap r0 = go (Map.singleton r0 0) IntMap.empty [(r0, 0)]
  where
    go ids trans [] =
        Just
            Compiled
                { compNull = IntMap.fromList [(i, nullable r) | (r, i) <- Map.toList ids]
                , compTrans = trans
                , compDense = IntMap.map dense trans
                , compStart = 0
                }
      where
        dense row =
            listArray (0, 255) [pick (toEnum k) row | k <- [0 .. 255 :: Int]]
        pick c row = head [j | (cls, j) <- row, inCls c cls]
    go ids trans ((r, i) : queue)
        | Map.size ids > cap = Nothing
        | otherwise =
            -- Thread only the NEWLY discovered states through the fold; an
            -- earlier version threaded the whole queue and then appended it
            -- to itself, doubling it per step (found by probe-compile.hs:
            -- even a bare Sym looped forever on gigabytes).
            let outs = [(cls, deriv (repChar cls) r) | cls <- classes r]
                step ((ids', new), acc) (cls, r') = case Map.lookup r' ids' of
                    Just j -> ((ids', new), (cls, j) : acc)
                    Nothing ->
                        let j = Map.size ids'
                        in ((Map.insert r' j ids', (r', j) : new), (cls, j) : acc)
                ((ids1, new1), row) = foldl' step ((ids, []), []) outs
            in go ids1 (IntMap.insert i row trans) (queue ++ reverse new1)

-- | Byte-level matcher: walks a strict ByteString through the dense
-- tables only (every byte is < 256).  Byte semantics: each byte is the
-- character with that code (latin-1 view); the String matchers remain the
-- reference for full Char semantics.
matchCompiledBS :: B.ByteString -> Compiled -> Bool
matchCompiledBS bs comp = go (compStart comp) 0
  where
    n = B.length bs
    go !i !pos
        | pos >= n = compNull comp IntMap.! i
        | otherwise =
            go
                ((compDense comp IntMap.! i) UA.! fromIntegral (B.index bs pos))
                (pos + 1)

matchCompiled :: Compiled -> String -> Bool
matchCompiled comp = go (compStart comp)
  where
    go i [] = compNull comp IntMap.! i
    go i (c : cs)
        | k < 256 = go ((compDense comp IntMap.! i) UA.! k) cs
        | otherwise =
            case [j | (cls, j) <- compTrans comp IntMap.! i, inCls c cls] of
                (j : _) -> go j cs
                [] -> False  -- unreachable: classes partition the alphabet
      where
        k = fromEnum c

-- | Right quotient by a string: @rightQuotient u r@ matches @s@ iff @r@
-- matches @s ++ u@.
rightQuotient :: String -> RE -> RE
rightQuotient u = rev . quotient (reverse u) . rev

-- | Language reversal.  Commutes syntactically with the whole algebra
-- (complement and intersection included); concatenation flips, and
-- @rev (h⁻¹ L) = h̃⁻¹ (rev L)@ where @h̃ c = reverse (h c)@.
rev :: RE -> RE
rev = \case
    Sym cls -> Sym cls
    Alt rs -> altL (map rev (Set.toList rs))
    Cut rs -> cutL (map rev (Set.toList rs))
    Seq rs -> seqL (map rev (reverse rs))
    Rep r -> rep_ (rev r)
    Not r -> not_ (rev r)
    InvHom m r -> invHom (Map.map reverse m) (rev r)
    Machine f q -> revMachine f q
    Eps -> Eps
    Nil -> Nil

-- | Reversal of a machine node: subset-construct the reversed automaton.
-- Start set = accepting states; a subset accepts iff it contains the
-- original current state; transitions are preimages.  Characters the
-- machine never tabulates behave uniformly (they all take state @p@ to its
-- 'fsmElse' target), so one reversed else-transition covers them all.
-- Worst case 2^|Q| subsets — machine nodes are expected to be small.
revMachine :: Fsm -> Int -> RE
revMachine f q0
    | Set.null start = Nil
    | otherwise = machineAt reversed (idOf start)
  where
    start = fsmAccept f
    sigma = Set.toList (Set.fromList [c | (_, c) <- Map.keys (fsmTrans f)])
    states =
        Set.toList $
            Set.unions
                [ Set.fromList (concat [[p, t] | ((p, _), t) <- Map.toList (fsmTrans f)])
                , Set.fromList (concat [[p, t] | (p, t) <- Map.toList (fsmElse f)])
                , fsmAccept f
                , Set.singleton q0
                ]
    pre s c = Set.fromList [p | p <- states, stepFsm f p c `Set.member` s]
    preElse s =
        Set.fromList
            [p | p <- states, Map.findWithDefault (-1) p (fsmElse f) `Set.member` s]

    -- BFS over reachable subsets, numbering them.
    explore seen [] = seen
    explore seen (s : rest)
        | s `Map.member` seen = explore seen rest
        | otherwise =
            explore
                (Map.insert s (Map.size seen) seen)
                (rest ++ [t | t <- preElse s : [pre s c | c <- sigma], not (Set.null t)])
    numbering = explore Map.empty [start]
    idOf s = Map.findWithDefault (-1) s numbering
    reversed =
        Fsm
            { fsmTrans =
                Map.fromList
                    [ ((i, c), idOf (pre s c))
                    | (s, i) <- Map.toList numbering
                    , c <- sigma
                    ]
            , fsmElse =
                Map.fromList
                    [(i, idOf (preElse s)) | (s, i) <- Map.toList numbering]
            , fsmAccept =
                Set.fromList
                    [i | (s, i) <- Map.toList numbering, q0 `Set.member` s]
            }

-- | Inverse homomorphism: @invHom h r@ matches @s@ iff @r@ matches
-- @concatMap h s@.  Characters absent from the map map to themselves, so
-- identity entries are dropped and a fully-identity map collapses to the
-- bare regex (design review 1.3: canonical form, not just boundedness).
invHom :: Map Char String -> RE -> RE
invHom _ Nil = Nil
invHom m r
    | Map.null m' = r
    | otherwise = InvHom m' r
  where
    m' = Map.filterWithKey (\c s -> s /= [c]) m

applyHom :: Map Char String -> Char -> String
applyHom m c = Map.findWithDefault [c] c m

-- | Node count, used to cap sizes in tests.
size :: RE -> Int
size r = 1 + sum (map size (children r))

children :: RE -> [RE]
children = \case
    Alt rs -> Set.toList rs
    Cut rs -> Set.toList rs
    Seq rs -> rs
    Rep r -> [r]
    Not r -> [r]
    InvHom _ r -> [r]
    Machine _ _ -> []
    _ -> []
