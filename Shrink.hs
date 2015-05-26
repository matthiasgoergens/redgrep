{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Shrink where

import Final
import Test.QuickCheck

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
