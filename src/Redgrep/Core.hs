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
      -- * The engine
    , nullable
    , deriv
    , match
    , matchMemo
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
    | Eps
    | Nil
    deriving (Eq, Ord, Show)

-- | @¬∅@: the universal language @Σ*@, the unit of 'cutL'.
top :: RE
top = Not Nil

sym :: Cls -> RE
sym (Pos s) | Set.null s = Nil
sym cls = Sym cls

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

-- | Left quotient by a string: @quotient u r@ matches @s@ iff @r@ matches
-- @u ++ s@.  This is just an iterated derivative.
quotient :: String -> RE -> RE
quotient u r = foldl' (flip deriv) r u

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
    Eps -> Eps
    Nil -> Nil

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
    _ -> []
