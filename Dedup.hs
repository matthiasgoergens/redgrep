{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
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
    deriving (Eq, Ord, Show)

-- in the beginning: collect = Maybe
-- But also possible data Collect context x = Maybe (context, x)
data Dup state f s =
    Dup { now :: forall context . state context -> Maybe (context, Either f s)
        , new :: forall context . context -> state context
        , empty :: forall context . state context
        , next :: forall context . Char -> state context -> state context
        -- , cmp :: forall context . state context -> state context -> Ordering
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
        -- , cmp = comparing (fmap snd . unMaybe')
        , merge = \a b -> maximumBy (comparing $ fmap snd . unMaybe') [a,b]
        }
instance Eps (Dup (Maybe' (Either () ()))) where
    eps = Dup
        { now = unMaybe'
        , new = Maybe' . Just . flip (,) (Right ())
        , empty = Maybe' Nothing
        , next = \char (Maybe' st) -> Maybe' $ (fmap.(<$)) (Left ()) st
        -- , cmp = comparing (fmap snd . unMaybe')
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
        -- , cmp = comparing (fmap snd . unMaybe')
        -- NB: Only works because Before is maximal constructor of SymE.
        -- TODO: This is wrong.  Left Before is still valid, even if Right Char is around.
        , merge = \a b -> maximumBy (comparing $ fmap snd . unMaybe') [a, b]
        }
data StateAlt state stateB context = StateAlt (state context) (stateB context)
alt_ :: Dup state f s -> Dup stateB f' s' -> Dup (StateAlt state stateB) (CutI f f') (AltI s s')
alt_ a b = Dup
    { now = \(StateAlt sa sb) -> 
        case (now a sa, now b sb) of
            (Nothing, Nothing) -> Nothing
            (Just (c, Right sa), _) -> Just (c, Right $ AltL sa)
            -- Which c[ontext] to take?
            -- (Just (c, Right sa), Just (c, Right sb)) -> Just (c, Right $ AltB sa sb)
            (_, Just (c, Right sb)) -> Just (c, Right $ AltR sb)
            -- TODO: The types are all over the place here.  Not tight about our constraints at all!
            (Just (c, Left fa), Just (c_, Left fb)) -> Just (c, Left $ Cut fa fb)
    , new = \context -> StateAlt (new a context) (new b context)
    , empty = StateAlt (empty a) (empty b)
    , next = \char (StateAlt sa sb) -> StateAlt (next a char sa) (next b char sb)
    , merge = \(StateAlt s sb) (StateAlt s' sb') -> StateAlt (merge a s s') (merge b sb sb')
    }

data State_ state stateB s context = State_ (state context) (stateB (context, s))
seq_ :: Dup state f s -> Dup stateB f' s'
    -> Dup (State_ state stateB s) (AltI f (SeqI s f')) (SeqI s s')
seq_ a b = Dup
    -- TODO: this is wrong!  As soon as we have a `new', we need a (Just _) `now'.
    { now =  \(State_ sa sb) ->
        let h ((c, s), Left f') =
                (c, Left (AltR (Seq s f')))
            h ((c, s), Right s') =
                (c, Right (Seq s s'))
        in fmap h $ (now b) sb
    , new = \c -> State_ (new a c) $ case now a (new a c) of
                Just (c, Right sa) -> new b (c, sa)
                _ -> empty b
    , empty = State_ (empty a) (empty b)
    , next = \char (State_ sta stb) ->
        let nb = next b char $
                    case now a sta of
                      Just (c, Right sa) -> merge b (new b (c, sa)) stb
                      _ -> stb
            na = next a char sta
        in State_ na nb
    -- , cmp = undefined
    -- Is this right?
    , merge = \(State_ s sb) (State_ s' sb') -> State_ (merge a s s') (merge b sb sb')
    }

sym'' :: Range -> Dup (Maybe' (Either SymE Char)) SymE Char
sym'' = sym
eps'' :: Dup (Maybe' (Either () ())) () ()
eps'' = eps
x = eps'' `seq_` eps''

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

-- need to break up states (+)
-- so that we can intersect them (*)

-- because nfa and power set construction: + -> *
-- {expression} = # states in DFA.
{a|b} = {a} * {b}
{a,b} = {a} * {b} -- implied by de-morgan.
-- sequencing
{a b} = {a} *? {b}
{!a} = {a}

-- repetition:
{a*} = {a} +? 1

-- de-morgan:
!(a|b) = (!a , !b)

(a+b) * (c+d)
(a*c) + (a*d) + (b*c) + (b*d)

-- nfa:
-- [expression] = # states in NFA
[a+b] = [a] +  [b]
[a*b] = [a] +? [b]
[a*b] = [a] *  [b]

nfa   dfa   co-nfa
--- = --- = ------
alt    1     cut

in    nfa states split.
in co-nfa states merge.

   nfa guesses one for success (on alt).
co-nfa guesses one for failure (on cut).

multi goto vs multi come-from.

We want nfa ^ co-nfa (like np ^ co-np).

what happens if we reverse edges of our automaton?

First, similarity:
    We only need to be able to keep a Set of regular sub-expressions around for union.
    and then only for unions of the same type.

    similarity is weaker than equality, but enough to give us a finite number of types.

{-
d :: Eq a => a -> Re a x -> Re a x
d c (Sym Nothing) = Eps c
d c (Sym (Just as))
    | c `elem` as = Eps c
    | otherwise = Nil
--- Nice symmetry!
d c (Alt a b) = Alt (d c a) (d c b)
d c (Cut a b) = Cut (d c a) (d c b)
-- This one grows.
-- d c (Seq a b) = Seq (d c a) b +++ Seq (v a) (d c b)
d c (Seq a b) = SeqL (d c a) b
        `union` SeqR (v a) (d c b)
-- This one grows.
-- rep a = repR (eps []) a
d c (Rep a) = seq (d c a) (Rep a)
d c (Not a) = Not (d c a)
d _ (Eps _) = Nil
d _ Nil = Nil
d c (FMap f x) = FMap f (d c x)
-}

main = return ()
