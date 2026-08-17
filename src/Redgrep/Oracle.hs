{-# LANGUAGE LambdaCase #-}

-- | The obviously-correct, obviously-slow membership semantics used as the
-- test oracle (see DESIGN.md).  Exponential in the string length: 'Seq'
-- tries every split, 'Rep' every nonempty first chunk.  Only ever applied to
-- small regexes and short strings; correctness over speed, always.
module Redgrep.Oracle
    ( member
    ) where

import qualified Data.Set as Set

import Redgrep.Core (RE(..), applyHom, inCls)

member :: RE -> String -> Bool
member re s = case re of
    Sym cls -> case s of
        [c] -> inCls c cls
        _ -> False
    Alt rs -> any (`member` s) (Set.toList rs)
    Cut rs -> all (`member` s) (Set.toList rs)
    Seq rs -> memberSeq rs s
    -- Requiring a nonempty first chunk loses no strings: any decomposition
    -- with empty chunks has the same concatenation as one without them.
    Rep r -> null s || any (\(a, b) -> member r a && member re b) (splits1 s)
    Not r -> not (member r s)
    InvHom m r -> member r (concatMap (applyHom m) s)
    Eps -> null s
    Nil -> False
  where
    memberSeq [] t = null t
    memberSeq (r : rs) t =
        any (\(a, b) -> member r a && memberSeq rs b) (splits t)
    splits t = [splitAt i t | i <- [0 .. length t]]
    splits1 t = [splitAt i t | i <- [1 .. length t]]
