{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Shrink where
import Prelude hiding (seq, not)

import Final
import Test.QuickCheck
import Data.Bifunctor

shrink' :: forall f s . REini f s -> [REini f s]
shrink' (SymX r) = (SymX <$> shrink r) ++ [EpsX TooMany 'a', NilX TooMany]
shrink' (AltX x y) =
    (AltX <$> shrink' x <*> shrink' y)
    ++ (AltX x <$> shrink' y)
    ++ (AltX <$> shrink' x <*> pure y)
shrink' (CutX x y) =
    (CutX <$> shrink' x <*> shrink' y)
    ++ (CutX x <$> shrink' y)
    ++ (CutX <$> shrink' x <*> pure y)
shrink' (SeqX x y) =
    (SeqX <$> shrink' x <*> shrink' y)
    ++ (SeqX x <$> shrink' y)
    ++ (SeqX <$> shrink' x <*> pure y)
shrink' (RepX x) =
    Bimap (Seq (Rep [])) (Rep . (:[])) x
    : (RepX <$> shrink' x)
shrink' (NotX x) =
    NotX <$> shrink' x
shrink' (EpsX f s) = [NilX f]
shrink' (NilX f) = []
shrink' (Bimap f s x) = Bimap f s <$> shrink' x

data Shield r = forall f s . Shield (r f s)

out :: Bifunctor r => Shield r -> r () ()
out (Shield r) = bimap (const ()) (const ()) r


altS, cutS :: RE r => Shield r -> Shield r -> Shield r
altS (Shield x) (Shield y) = Shield (alt x y)
cutS (Shield x) (Shield y) = Shield (cut x y)
seqS (Shield x) (Shield y) = Shield (seq x y)

repS (Shield x) = Shield (rep x)
notS (Shield x) = Shield (not x)

shrink2 op (Shield x) (Shield y)
    = Shield nil_ : Shield eps_ : Shield x : Shield y
    : tail (op <$> shrinkS' (Shield x) <*> shrinkS' (Shield y))
shrink1 op (Shield x)
    = Shield nil_ : Shield eps_
    : (op <$> shrinkS (Shield x))

shrinkS' :: Shield REini -> [Shield REini]
shrinkS' x = x : shrinkS x

shrinkS :: Shield REini -> [Shield REini]
shrinkS (Shield (SymX r))
    = Shield nil_
    : Shield eps_
    : (Shield . SymX <$> shrink r)
shrinkS (Shield (AltX x y))
    = shrink2 altS (Shield x) (Shield y)
shrinkS (Shield (CutX x y))
    = shrink2 cutS (Shield x) (Shield y)
shrinkS (Shield (SeqX x y))
    = shrink2 seqS (Shield x) (Shield y)
shrinkS (Shield (RepX x))
    = shrink1 repS (Shield x)
shrinkS (Shield (NotX x))
    = shrink1 notS (Shield x)
shrinkS (Shield (EpsX f s))
    = [Shield $ NilX f]
shrinkS (Shield (NilX f))
    = []
