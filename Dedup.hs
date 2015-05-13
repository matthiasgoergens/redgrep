{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
import Final hiding (main)
import Control.Applicative hiding (empty)
import Control.Monad
import Prelude hiding (seq, not)
import qualified Prelude as P
import qualified Types as T
import Util
import Data.List
import Data.String
import Data.Biapplicative
import Data.Bifunctor
import Data.Function (on)
import Data.Ord
import Control.Arrow ((***))

{-
    :: (state, context)
    (add) start-state (with context)
    char -> state -> state
    merge states of same type, keep context of choice (or merge contexts, too)
    because of non-determinism: state ~ states
-}

data Context a b = Maybe (a, b)

-- in the beginning: collect = Maybe
-- But also possible data Collect context x = Maybe (context, x)
data Dup state f s =
    Dup { now :: forall context . state context -> Maybe (context, Either f s)
        , new :: forall context . context -> state context
        , empty :: forall context . state context
        , next :: forall context . Char -> state context -> state context
        , cmp :: forall context . state context -> state context -> Ordering
        , merge :: forall context . state context -> state context -> state context
        }
-- ((), a) isomorph to a, but I'm trying to see a pattern here.
newtype Maybe' a context = Maybe' { unMaybe' :: Maybe (context, a) }
instance Nil (Dup (Maybe' ())) where
    nil = Dup
        { now = fmap (id *** Left) . unMaybe'
        , new = Maybe' . Just . flip (,) ()
        , empty = Maybe' $ Nothing
        , next = \char st -> st
        , cmp = comparing (fmap snd . unMaybe')
        , merge = \a b -> maximumBy (comparing $ fmap snd . unMaybe') [a,b]
        }
instance Eps (Dup (Maybe' (Either () ()))) where
    eps = Dup
        { now = unMaybe'
        , new = Maybe' . Just . flip (,) (Right ())
        , empty = Maybe' Nothing
        , next = \char (Maybe' st) -> Maybe' $ (fmap.(<$)) (Left ()) st
        , cmp = comparing (fmap snd . unMaybe')
        , merge = \a b -> maximumBy (comparing $ fmap snd . unMaybe') [a,b]
        }
rangeMatch' :: Range -> Char -> Either SymE Char
rangeMatch' range char = maybe (Left $ Wrong range char) Right $ rangeMatch range char

instance Sym (Dup (Maybe' (Either SymE Char))) where
    sym range = Dup
        { now = unMaybe'
        , new = Maybe' . Just . flip (,) (Left Before)
        , empty = Maybe' Nothing
        , next = \char (Maybe' st) ->
            let helper char (Left Before) =
                    maybe (Left $ Wrong range char) Right $ rangeMatch range char
                helper _ _ = Left TooMany
            in Maybe' $ (fmap.fmap) (helper char) st
        , cmp = comparing (fmap snd . unMaybe')
        -- NB: Only works because Before is maximal constructor of SymE.
        , merge = \a b -> maximumBy (comparing $ fmap snd . unMaybe') [a, b]
        }
{-
-- seq_ :: Dup state f s -> Dup stateB fB sB
    -- -> Dup (state, stateB) (AltI f (SeqI s f')) (SeqI s s')
seq_ a b = Dup
    { now = now b . snd -- a lie!
    , new = \c -> (new a c, empty b)
    , empty = (empty a, empty b)
    , next = \char (sta, stb) ->
        let nb = next b char $
                    case now a sta of
                      Just (c, Right sa) -> merge b (new b _) stb
                      -- Just (c, Right sa) -> merge b (new b (c, sa)) stb
                      _ -> stb
            na = next a char sta
        in (na, nb)
    , cmp = undefined
    , merge = undefined
    }
-}

-- instance Eq (Dup collect state f s) where
-- instance Ord (Dup collect state f s) where
-- merge, or only addNew?
-- then, also need to merge tuples.

-- instance Seq (Dup state) where
    -- seq :: r f s -> r f' s' -> r (AltI f (SeqI s f')) (SeqI s s')
{-
seqI a b = Dup
    { now = undefined (now a) (now b)
    , next = \_ _ -> undefined
    , state = (state a, state b)
    }
-}
{-
--- no, vs start (vs nil)
seq origa origb = Constructor $ (\context ->
    let a = singleton origa context
        b = null origb
        result = seq' $ result $ origb $ rresult a
-- d c (Seq a b) = SeqL (d c a) b `union` SeqR (v a) (d c b)
    let origa' = origa context
    let push (Dedup _ a' b') char =
         let a' = push a char context
             -- rresult :: Stuff -> Either fail succ
             rresult :: Stuff -> Maybe r
             rresult = either (const Nothing) Just <=< result
             -- union should be idempotent.
             b_ = maybe id (union . origb) (rstate a) b
             b' = push b_ char
            (Dedup result a' b')
-}
        
{-        
d :: Eq a => a -> Re a x -> Re a x
d c (Sym Nothing) = Eps c
d c (Sym (Just as))
    | c `elem` as = Eps c
    | otherwise = Nil
d c (Alt a b) = Alt (d c a) (d c b)
d c (Cut a b) = Cut (d c a) (d c b)
-- This one grows.
-- d c (Seq a b) = Seq (d c a) b +++ Seq (v a) (d c b)
d c (Seq a b) = SeqL (d c a) b `union` SeqR (v a) (d c b)
-- This one grows.
-- rep a = repR (eps []) a
d c (Rep a) = seq (d c a) (Rep a)
d c (Not a) = Not (d c a)
d _ (Eps _) = Nil
d _ Nil = Nil
d c (FMap f x) = FMap f (d c x)
-}

main = return ()
