{-# LANGUAGE GADTs,TupleSections,TemplateHaskell #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
module Main where
-- import Data.Foldable hiding (fold, concatMap, foldr, elem, foldl, mapM_)
import Prelude hiding (sequence, mapM)
import Data.List (sort)
import Data.Monoid
import qualified Data.Set as Set
import Data.Ord
import Data.Typeable
import Control.Applicative
-- TODO: Look into lenses.
import Test.QuickCheck
import Test.QuickCheck.Function
import Test.QuickCheck.All

import Control.Arrow
import Control.Monad


data Re a x where
    -- Ranges of letters.  Nothing stands for .
    -- TODO: Add character classes later.
    Sym :: Maybe [a] -> Re a a
    -- Alternative, |
    Alt :: Re a x -> Re a y -> Re a (Either x y)
    -- Intersection
    Cut :: Re a x -> Re a y -> Re a (x,y)
    -- Sequencing
    Seq :: Re a x -> Re a y -> Re a (x,y)
    -- Repetition, Kleene Star *
    Rep :: Re a x -> Re a [x]
    -- Complement
    Not :: Re a x -> Re a ()
    -- Match empty string
    Eps :: x -> Re a x
    -- Match no string
    Nil :: Re a x
    FMap :: (x -> y) -> Re a x -> Re a y
    deriving (Typeable)

fold
    :: forall a b x
    .  (Maybe [a] -> b) -- Sym
    -> (b -> b -> b) -- Alt
    -> (b -> b -> b) -- Cut
    -> (b -> b -> b) -- Seq
    -> (b -> b) -- Rep
    -> (b -> b) -- Not
    -> b -- Eps (possible to do more?)
    -> b -- Nil
    -> (b -> b) -- FMap
    -> Re a x -> b
fold sym alt cut seq rep not eps nil fmap =
    let h :: forall y. Re a y -> b
        h re = case re of
            Sym char -> sym char
            Alt x y -> alt (h x) (h y)
            Cut x y -> cut (h x) (h y)
            Seq x y -> seq (h x) (h y)
            Rep x -> rep (h x)
            Not x -> not (h x)
            Eps _ -> eps
            Nil -> nil
            FMap _ x -> fmap (h x)
    in h

size :: Re a x -> Int
size = fold (const 1) p p p (1+) (1+) 1 1 (1+) where
    p a b = a + 1 + b

height :: Re a x -> Int
height = fold (const 1) m m m (1+) (1+) 1 1 (1+) where
    m a b = 1 + max a b

-- Just for testing incomplete pattern match warning and GADTs.
{-
ttt :: Re a [x] -> Int
ttt (FMap _ _) = 0
ttt (Eps _) = 1
ttt (Rep _) = 2
ttt Nil = 4
ttt (Sym _) = 5 -- This doesn't always work.
-}

(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) f g a b = f (g a b)

-- How to define Arbitrary instances?
-- CoArbitrary via Show?
instance (Arbitrary a, Applicative m, Monoid (m a), Arbitrary (m a)) => Arbitrary (Re a (m a)) where
    arbitrary = oneof
        [ FMap pure . Sym <$> arbitrary
        , FMap (either id id) .: Alt <$> arbitrary <*> arbitrary 
        , FMap (uncurry mappend) .: Cut <$> arbitrary <*> arbitrary
        , FMap (uncurry mappend) .: Seq <$> arbitrary <*> arbitrary
        , FMap mconcat . Rep <$> arbitrary
        , FMap (const mempty) . Not <$> (arbitrary :: Gen (Re a (m a)))
        , Eps <$> arbitrary
        , pure Nil
        -- , FMap . apply <$> arbitrary <*> arbitrary
        ]
    -- shrink (Sym s) = Sym <$> shrink s
    -- shrink _ = []

instance (Arbitrary (Re Char x), Arbitrary (Re Char y)) => Arbitrary (Re Char (x,y)) where
    arbitrary = elements [Cut, Seq] <*> arbitrary <*> arbitrary

instance (Arbitrary (Re Char x), Arbitrary (Re Char y)) => Arbitrary (Re Char (Either x y)) where
    arbitrary = Alt <$> arbitrary <*> arbitrary

-- How to do Not and Eps and Nil?

-- deriving instance Show (ReX a x)
-- deriving instance Eq (ReX a x)
-- deriving instance Ord (ReX a x)

instance Show c => Show (Re c x) where
    show re = case re of
        Sym Nothing -> "."
        Sym (Just [x]) -> show x
        Sym (Just xs) -> "[" ++ concatMap show xs ++ "]"
        Alt a b -> show a ++ "|" ++ show b
        Cut a b -> show a ++ "&" ++ show b
        Seq a b -> show a ++ show b
        Rep a -> show a ++ "*"
        Not a -> "!" ++ show a
        Eps _ -> "ε"
        Nil -> "∅"
        FMap _ a -> "$" ++ show a -- Not great.

-- Something wrong here.
-- n r === does r accept the empty string?
n :: Re a x -> Bool
n (Sym _) = False
n (Alt a b) = n a || n b
n (Cut a b) = n a && n b
n (Seq a b) = n a && n b
n (Rep _) = True
n (Not a) = not (n a) -- not convinced.
n (Eps _) = True
n Nil = False
n (FMap _ x) = n x

n' :: Re a x -> Maybe x
n' (Sym _) = Nothing
n' (Alt a b) = (Left <$> n' a) <|> (Right <$> n' b)
n' (Cut a b) = liftA2 (,) (n' a) (n' b)
n' (Seq a b) = liftA2 (,) (n' a) (n' b)
-- Could also just always give []
n' (Rep a) = fmap (:[]) (n' a) <|> Just []
n' (Not a) = maybe (Just ()) (const Nothing) $ n' a
n' (Eps x) = Just x
n' Nil = Nothing
n' (FMap f x) = fmap f (n' x)

v :: Re a x -> Re a x
v = maybe Nil Eps . n'

-- float up FMap?
-- Existentials might do the trick.  Or, rather, necessary for something else.
-- a :: Re a x -> (y -> x, Re a y)
{-
a :: Re a x -> Re a x
a (FMap f x) = case a x of
    FMap g y -> FMap (f.g) y
    x -> FMap f x
a (Sym x) = Sym x
a (Alt x y) = case (a x, a y) of
    (FMap f x, FMap g y) -> FMap (mapBoth f g) (Alt x y)
    (FMap f x,        y) -> FMap (mapLeft f)   (Alt x y)
    (       x, FMap g y) -> FMap (mapRight  g) (Alt x y)
-}

prop_simplify :: Re Char String -> Bool
prop_simplify re = descending . take 100 . map size $ iterate simplify re where
    descending l = l == reverse (sort l)


simplify :: forall a x . Eq a => Re a x -> Re a x
-- Lenses or boilerplate scrapping?
simplify = s where
  s :: forall y . Re a y -> Re a y
  s re = case re of
    Alt Nil x -> FMap Right (s x)
    Alt x Nil -> FMap Left (s x)

    Cut Nil _ -> Nil
    Cut _ Nil -> Nil
    Cut (Not Nil) x -> FMap ((),) (s x)
    Cut x (Not Nil) -> FMap (,()) (s x)

    Cut (Eps x) y -> FMap (x,) (v y)
    Cut x (Eps y) -> FMap (,y) (v x)

    Seq (Eps x) y -> FMap (x,) (s y)
    Seq x (Eps y) -> FMap (,y) (s x)
    Seq Nil _ -> Nil
    Seq _ Nil -> Nil
    Rep Nil -> Eps []
    -- We've got a choice here.
    Rep (Eps _) -> Eps []
    -- Rep (Eps x) -> Eps [x,..]
    -- We've got a choice here!
    Rep (Rep a) -> FMap (:[]) $ Rep a
    -- Rep (Rep a) -> Rep $ FMap (:[]) a

    -- -- TODO: Figure out the type magic here.
    -- This can be pretty inefficient.
    -- Seq (Rep a) (Rep b) | _ a == b -> FMap (const ([],[])) $ Rep a
    -- Seq (Rep a) (Rep b) -> FMap (const ([],[])) $ Rep a
    Not (Not x) -> FMap (const ()) (s x)
    -- catch all:
    Sym x -> Sym x
    Eps x -> Eps x
    Nil -> Nil
    FMap f (FMap g x) -> FMap (f . g) (s x)
    FMap f x -> FMap f (s x)
    Alt x y -> Alt (s x) (s y)
    -- Cut Sym Sym would be useful.
    Cut x y ->  Cut (s x) (s y)
    Seq x y -> Seq (s x) (s y)
    Rep x -> Rep (s x)
    Not x -> Not (s x)
-- simplify = foldRe1 simplify1

-- type C2 a = Re a x -> Re a -> Re a
-- type C1 a x = Re a x -> Re a x
-- foldRe1 :: C1 a x -> C1 a x
-- -- Needs more typing magic!
{-
foldRe1 s =
    let f re = s $ case re of
            Sym x -> Sym x
            (Alt a b) -> Alt (f a) (f b)
            (Cut a b) -> Cut (f a) (f b)
            (Seq a b) -> Seq (f a) (f b)
            (Rep a) -> Rep (f a)
            (Not a) -> Not (f a)
            Eps -> Eps
            Nil -> Nil
    in f
-}

-- d takes the derivative.  The heart of the matcher!

-- We have to prove that a derivative doesn't grow the regex
-- beyond some measure.

d :: Eq a => a -> Re a x -> Re a x
d c (Sym Nothing) = Eps c
d c (Sym (Just as))
    | c `elem` as = Eps c
    | otherwise = Nil
d c (Alt a b) = Alt (d c a) (d c b)
d c (Cut a b) = Cut (d c a) (d c b)
-- This one grows.
d c (Seq a b) = FMap (either id id) $ Seq (d c a) b `Alt` Seq (v a) (d c b)
-- This one grows.
d c (Rep a) = FMap (uncurry (:)) $ Seq (d c a) (Rep a)
d c (Not a) = Not (d c a)
d _ (Eps _) = Nil
d _ Nil = Nil
d c (FMap f x) = FMap f (d c x)

-- So, let's concentrate our attention on Rep and Seq, the two main culprits.
-- Everything else looks intuitively, like it wouldn't change some measure
-- of complexity. (They mostly just commute with d.)



-- Pass to float up FMaps? --- especially needed for minimization.

cmp :: Ord a => [a] -> [a] -> Ordering
cmp = comparing (length &&& id)

{-
-- TODO: prefix trees should actually work better.
-- Need to produce ordered list of results.  Order by (length &&& id)
-- Nothing stands for: don't care.
enumerate, en :: Ord a => Re a x -> [[Maybe a]]
enumerate = en
en (Sym x) = sortBy cmp $ fmap pure $ sequenceA x
-- Will get some strings twice.
en (Alt x y) = mergeBy cmp (en x) (en y)
en (Cut x y) = isectBy cmp (en x) (en y)
-- en (Rep x) = _ -- like Seq?
-- en (Seq x y) = _ -- mergeAllBy and fmap traverse
-- en (Not x) = _ -- opposite of intersect..
en (Eps x) = [[]]
en Nil = []
en (FMap _ x) = en x
-}

-- next item of interest, doesn't lead to a match in general.
next :: Ord a => Re a x -> Set a
next (Sym xs) = maybe mempty fromList xs
next (Alt x y) = union (next x) (next y)
next (Cut x y) = union (next x) (next y)
next (Seq x y) = (if n x then union (next y) else id) (next x)
next (Rep x) = next x
-- If we were not just interested in any item of interest,
-- but in what moves us forward, this would be broken.
-- We couldn't just operate on the next item.
-- We'd need something like the following, but cleverer:
-- next (Not x) = complement $ next x
next (Not x) = next x
next (Eps _) = mempty
next Nil = mempty
next (FMap _ x) = next x

-- TODO:  Put into own module!  Sets with omega.
-- TODO: QuickCheck
-- Left x === \Omega - x
-- Right x === x
newtype Set a = Set (Either (Set.Set a) (Set.Set a))
    deriving (Show, Ord, Eq)
union :: Ord a => Set a -> Set a -> Set a
union (Set a) (Set b) = Set $ case (a,b) of
    (Left a, Left b) -> Left $ Set.intersection a b
    (Left a, Right b) -> Left $ a Set.\\ b
    (Right a, Left b) -> Left $ b Set.\\ a
    (Right a, Right b) -> Right $ Set.union a b
intersection :: Ord a => Set a -> Set a -> Set a
intersection (Set a) (Set b) = Set $ case (a,b) of
    (Left a, Left b) -> Left $ Set.union a b
    (Left a, Right b) -> Right $ b Set.\\ a
    (Right a, Left b) -> Right $ a Set.\\ b
    (Right a, Right b) -> Right $ Set.intersection a b
complement :: Set a -> Set a
complement (Set a) = Set $ case a of
    Left a -> Right a
    Right a -> Left a
omega :: Ord a => Set a
omega = Set $ Left mempty
fromList :: Ord a => [a] -> Set a
fromList = Set . Right . Set.fromList
-- TODO: Functor instance?  Possible exactly iff we have a Functor instance for Set.Set
instance Ord a => Monoid (Set a) where
    mempty = Set $ Right mempty
    mappend = union
    
-- empty :: Set a
-- empty = Right empty


instance Functor (Re a) where
    -- We could do something more clever, by recursing.
    fmap = FMap

-- Ha, this is almost trivial!
instance Applicative (Re a) where
    pure = Eps 
    f <*> a = FMap (uncurry ($)) $ Seq f a
    a <* b = FMap fst $ Seq a b
    a *> b = FMap snd $ Seq a b
instance Alternative (Re a) where
    empty = Nil
    a <|> b = FMap (either id id) $ Alt a b
    some x = FMap (uncurry (:)) $ Seq x (Rep x)
    many = Rep

ds :: Eq a => a -> Re a x -> Re a x
ds c = simplify . d c . simplify

-- -- This should not be possible to define sensibly.
instance Monad (Re a) where
    (>>=) = undefined
    return = pure

-- flapping' :: Re Char
flapping' :: Re Char ()
flapping' = simplify . FMap (const ()) $ Cut
    (Not $ dots `Seq` str "flapping" `Seq` dots)
    (dots `Seq` str "ping" `Seq` dots)

-- flapping :: Re Char
-- flapping' = not (dots . "flap") . ping . dots
flapping :: Re Char String
flapping = FMap (const []) $ Not (dots `Seq` str "flap")
           `Seq` str "ping"
           `Seq` dots

opts :: Re a y -> Re a (Maybe y)
opts = FMap (either (const Nothing) Just) . Alt (Eps ())
-- seqs = foldr Seq (Eps ())

match :: Eq a => Re a x -> [a] -> Bool
match re = n . foldl (flip ds) re
match' :: Eq a => Re a x -> [a] -> Maybe x
match' re = n' . foldl (flip ds) re
matchn :: Eq a => Re a x -> [a] -> [Re a x]
matchn  = scanl (flip ds)

matchn' :: Eq a => Re a x -> [a] -> [(Re a x, Maybe x)]
matchn' re s = fmap (id&&&n') $ matchn re s

sym :: [a] -> Re a a
sym = Sym . return

str :: [a] -> Re a [a]
str = foldr (\a b -> FMap (uncurry (:)) $ Seq a b) (Eps []) . map (Sym . Just . (:[]))

dots :: Re a [a]
dots = Rep (Sym Nothing)
dot :: Re a a
dot = Sym Nothing
pp :: Re Char [Char] -> IO ()
pp = putStrLn . show

prop_match_noincrease :: Re Char String -> String -> Bool
prop_match_noincrease re s = descending $ map size $ matchn re s where
    descending l = l == reverse (sort l)

return []
runTests = $quickCheckAll

main :: IO ()
main = void $ do
    runTests

main' = do
    print $ match (sym "a") "a"
    print $ match (Rep (sym "a")) "aaaaaba"
    mapM_ pp $ matchn (Rep (sym "a")) "aaaaaba"
    putStrLn ""
    mapM_ pp $ matchn dots "aaaaaba"
    putStrLn "---"
    let s = "xflappinge ping blub"
    mapM_ pp $ matchn flapping s
    print "match:"
    print $ match' flapping s
    print "/match"
    mapM_ print $ matchn' (Rep $ Rep $ Sym $ Just "a") "a"
    print $ match' (many $ many $ Sym $ Just "a") "a"
    print $ match' (many $ fmap (either id id) $ Alt Nil $ many $ Sym $ Just "a") "a"
    print $ next flapping
    print $ next $ Not $ str "ab"

    let r = simplify $ many $ FMap (const 1) $ many $ Sym $ Just "a"
    print $ map height $ matchn r "aaaaaaaaaa"
    print $ map size $ matchn r "aaaaaaaaaa"
    mapM_ print $ matchn r "aaaaaaaaaa"

    -- print $ match (Not (str "flapping")) "flapping"
    -- print $ match (dots `Seq` (Not $ str "flapping")) "flapping"
