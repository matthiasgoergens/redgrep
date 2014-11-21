{-# LANGUAGE GADTs,TupleSections,TemplateHaskell,ViewPatterns #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
module Main where
-- import Data.Foldable hiding (fold, concatMap, foldr, elem, foldl, mapM_)
import Prelude hiding (sequence, mapM)
import Data.List (sort)
import Data.Monoid
import Data.Maybe (isJust)
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

import Debug.Trace (trace)


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

same :: forall a x y . (Eq a) => Re a x -> Re a y -> Maybe (Re a (x,y))
same a b = floatFMap a # floatFMap b where
    (#) :: forall x y . Re a x -> Re a y -> Maybe (Re a (x,y))
    (Sym a)   # (Sym x) | a == x = Just $ FMap (id&&&id) $ Sym a
    (Alt a b) # (Alt x y) = FMap (either (Left *** Left) (Right *** Right)) .: Alt <$> (a # x) <*> (b # y)
    (Cut a b) # (Cut x y) = FMap r .: Cut <$> (a # x) <*> (b # y)
    (Seq a b) # (Seq x y) = FMap r .: Seq <$> (a # x) <*> (b # y)
    (Rep a)   # (Rep x)   = FMap unzip . Rep <$> (a # x)
    (Not a)   # (Not x)   = FMap (const ((),())) . Not <$> (a # x)
    (Eps a)   # (Eps x)   = Just $ Eps (a, x)
    Nil       # Nil       = Just Nil
    (FMap f x) # (FMap g y) = FMap (f *** g) <$> (x # y)
    _ # _ = Nothing

    r ((a,x),(b,y)) = ((a,b),(x,y))

prop_same :: Re Char [Char] -> Bool
prop_same re = isJust (same re re)

prop_same_fm :: Re Char [Char] -> Bool
prop_same_fm (floatFMap -> re) = isJust (same re re)

compareStructure :: forall a x y . Eq a => Re a x -> Re a y -> Bool
compareStructure a b = floatFMap a # floatFMap b where
    (#) :: forall x y . Re a x -> Re a y -> Bool
    (Sym a)   # (Sym x) = a == x
    (Alt a b) # (Alt x y) = a # x && b # y
    (Cut a b) # (Cut x y) = a # x && b # y
    (Seq a b) # (Seq x y) = a # x && b # y
    (Rep a)   # (Rep x)   = a # x
    (Not a)   # (Not x)   = a # x
    (Eps _)   # (Eps _)   = True
    Nil       # Nil       = True
    (FMap _ x) # (FMap _ y) = x # y
    _ # _ = False

floatFMap :: Re a x -> Re a x
floatFMap = fold' Sym alt cut seq rep not Eps Nil fmap where
    alt (FMap f x) (FMap g y) = FMap (f +++ g) $ Alt x y
    alt (FMap f x) y = FMap (left f) $ Alt x y
    alt x (FMap g y) = FMap (right g) $ Alt x y
    alt x y = Alt x y

    cut (FMap f x) (FMap g y) = FMap (f *** g) $ Cut x y
    cut (FMap f x) y = FMap (first f) $ Cut x y
    cut x (FMap g y) = FMap (second g) $ Cut x y
    cut x y = Cut x y

    seq (FMap f x) (FMap g y) = FMap (f *** g) $ Seq x y
    seq (FMap f x) y = FMap (first f) $ Seq x y
    seq x (FMap g y) = FMap (second g) $ Seq x y
    seq x y = Seq x y

    rep (FMap f x) = FMap (map f) $ Rep x
    rep x = Rep x

    not (FMap f x) = Not x
    not x = Not x

    fmap f (FMap g x) = FMap (f.g) x
    fmap f x = FMap f x

-- Just for testing
foldId :: Re a x -> Re a x
foldId = fold' Sym Alt Cut Seq Rep Not Eps Nil FMap

prop_foldID :: Re Char [Char] -> Bool
prop_foldID re = show re == show (foldId re)

fold'
    :: forall a
    .  (Maybe [a] -> Re a a) -- Sym
    -> (forall x y . Re a x -> Re a y -> Re a (Either x y)) -- Alt
    -> (forall x y . Re a x -> Re a y -> Re a (x,y)) -- Cut
    -> (forall x y . Re a x -> Re a y -> Re a (x,y)) -- Seq
    -> (forall x . Re a x -> Re a [x]) -- Rep
    -> (forall x . Re a x -> Re a ()) -- Not
    -> (forall x . x -> Re a x) -- Eps
    -> (forall x . Re a x) -- Nil
    -> (forall x y . (x -> y) -> Re a x -> Re a y) -- FMap
    -> forall x . Re a x -> Re a x
fold' sym alt cut seq rep not eps nil fmap =
    let h :: forall y. Re a y -> Re a y
        h re = case re of
            Sym char -> sym char
            Alt x y -> alt (h x) (h y)
            Cut x y -> cut (h x) (h y)
            Seq x y -> seq (h x) (h y)
            Rep x -> rep (h x)
            Not x -> not (h x)
            Eps x -> eps x
            Nil -> nil
            FMap f x -> fmap f (h x)
    in h

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
    let h :: forall y . Re a y -> b
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

(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) f g a b = f (g a b) 

size :: Re a x -> Int
size = fold (const 1) p p p (1+) (1+) 1 1 (1+) where
    p a b = a + 1 + b

statesDFA :: Re a x -> Int
statesDFA = fold (const 1) (+) (*) (*) id id 0 0 id

-- statesNnFA :: Re a x -> Int
-- statesNnFA = fold (const 1) (+) (+) (*) id id 0 0 id

height :: Re a x -> Int
height = fold (const 1) m m m (1+) (1+) 1 1 (1+) where
    m a b = 1 + max a b

starHeight :: Re a x -> Int
starHeight = fold (const 0) max max max (1+) id 0 0 id

-- each star might double the size of the underlying,
-- because d a .* = Seq (d a) a*
maxStarSize :: Re a x -> Int
maxStarSize = fold (const 1) p p p star (1+) 1 1 (1+) where
    p a b = a + 1 + b
    star = (\s -> 1 + (1 + s) + (1 + s))

prop_float_finite :: Re Char [Char] -> Bool
prop_float_finite re = length (show $ floatFMap re) >= 0

prop_floatFMapS :: Re Char [Char] -> Bool
prop_floatFMapS re = topFMap $ floatFMap re


prop_floatFMap_inSimplify :: Re Char [Char] -> Bool
prop_floatFMap_inSimplify re = topFMap $ simplify re

noFMap :: Re a x -> Bool
noFMap = fold (const True) (&&) (&&) (&&) id id True True (const False)

topFMap :: Re a x -> Bool
topFMap (FMap _ x) = noFMap x
topFMap x = noFMap x

-- Just for testing incomplete pattern match warning and GADTs.
{-
ttt :: Re a [x] -> Int
ttt (FMap _ _) = 0
ttt (Eps _) = 1
ttt (Rep _) = 2
ttt Nil = 4
ttt (Sym _) = 5 -- This doesn't always work.
-}

-- How to define Arbitrary instances?
-- CoArbitrary via Show?
instance (Arbitrary a, Applicative m, Monoid (m a), Arbitrary (m a), Eq a) => Arbitrary (Re a (m a)) where
    arbitrary = sized $ \n ->
        let simple = [ FMap pure . Sym <$> arbitrary
                     , Eps <$> arbitrary
                     , pure Nil ]
            r1 = resize (n-1)
            r2 = resize (n `div` 2)
            complex = [ r2 $ FMap (either id id) .: Alt <$> arbitrary <*> arbitrary
                      , r2 $ FMap (uncurry mappend) .: Cut <$> arbitrary <*> arbitrary
                      , r2 $ FMap (uncurry mappend) .: Seq <$> arbitrary <*> arbitrary
                      , r1 $ FMap mconcat . Rep <$> arbitrary
                      , r1 $ FMap (const mempty) . Not <$> (arbitrary :: Gen (Re a (m a)))
                      -- , r1 $ FMap . apply <$> arbitrary <*> arbitrary
                      ]
        in if n <= 0
        then oneof simple
        else oneof $ simple ++ complex

    shrink re = (let f = floatFMap re in if not (topFMap re) then (floatFMap re:) else id)
              . (let s = simplify re in if size s < size re then (s:) else id)
              $ shrink' re where

    -- shrink (Sym s) = Sym <$> shrink s
    -- shrink _ = []

shrink' :: forall a x . (Arbitrary a)  => Re a x -> [Re a x]
shrink' (Sym x) = (Sym <$> shrink x) ++ [Nil]
shrink' (Alt x y) = (FMap Left <$> shrink' x) ++ (FMap Right <$> shrink' y) ++ (Alt x <$> shrink' y) ++ (Alt <$> shrink' x <*> [y]) ++ [Nil]
shrink' (Cut x y) = (Cut <$> shrink' x <*> [y]) ++ (Cut x <$> shrink' y) ++ [Nil]
shrink' (Seq x y) = (Seq <$> shrink' x <*> [y]) ++ (Seq x <$> shrink' y) ++ [Nil]
shrink' (Rep x) = (Rep <$> shrink' x) ++ [Nil]
shrink' (Not x) = (Not <$> shrink' x) ++ [Nil]
-- Can't do arbitrary x, yet.
shrink' (Eps x) = [Nil]
shrink' Nil = []
-- How to shrink the function?
shrink' (FMap f (FMap g x)) = FMap (f . g) <$> shrink' x
shrink' (FMap f x) = FMap f <$> shrink' x


instance (Arbitrary (Re Char x), Arbitrary (Re Char y)) => Arbitrary (Re Char (x,y)) where
    arbitrary = elements [Cut, Seq] <*> arbitrary <*> arbitrary

instance (Arbitrary (Re Char x), Arbitrary (Re Char y)) => Arbitrary (Re Char (Either x y)) where
    arbitrary = Alt <$> arbitrary <*> arbitrary

-- How to do Not and Eps and Nil?

-- deriving instance Show (ReX a x)
-- deriving instance Eq (ReX a x)
-- deriving instance Ord (ReX a x)

instance Show Char => Show (Re Char x) where
    showsPrec d re = case re of
        Sym Nothing -> showString "."
        Sym (Just [x]) -> showsPrec d x
        Sym (Just xs) -> showString ("[" ++ init (tail $ show xs) ++ "]")
        Alt a b -> showParen (d > 5) $ showsPrec 6 a . showString "|" . showsPrec 6 b
        Cut a b -> showParen (d > 6) $ showsPrec 7 a . showString "&" . showsPrec 7 b
        Seq a b -> showParen (d > 10) $ showsPrec 11 a . showsPrec 11 b
        Rep a -> showParen (d > 9) $ showsPrec 10 a . showString "*"
        Not (Eps _) -> showParen (d > 8) $ showString ".+"
        Not Nil -> showParen (d > 8) $ showString ".*"
        Not a -> showParen (d > 8) $ showString "!" . showsPrec 9 a
        Eps _ -> showString "ε"
        Nil -> showString "∅"
        FMap _ a -> showParen (d > 8) $ showString "$" . showsPrec 9 a -- Not great.

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

prop_simplify_notBigger :: Re Char String -> Bool
prop_simplify_notBigger re = descending . take 100 . map size $ iterate simplify re where
    descending l = l == reverse (sort l)

prop_same_simplify :: Re Char [Char] -> Bool
prop_same_simplify (simplify -> re) = isJust (same re re)

simplify :: forall a x . Eq a => Re a x -> Re a x
-- Lenses or boilerplate scrapping?
simplify = (!!20) . iterate (floatFMap . fold' sym alt cut seq rep not eps nil fm)  where
    sym (Just []) = Nil
    sym x = Sym x

    alt Nil x = FMap Right x
    alt (Not Nil) _ = FMap Left $ Not Nil
    -- Not left-biased.
    alt _ (Not Nil) = FMap Right $ Not Nil
    alt x Nil = FMap Left x
    alt x (Eps _) | n x = FMap Left x
    -- Dubious, not left-biased.
    alt (Eps _) y | n y = FMap Right y
    alt x y | compareStructure x y = Left <$> x
    -- Might need to repeat?
    alt (Alt x y) z = FMap f $ Alt x (Alt y z) where
        f (Left x) = Left (Left x)
        f (Right (Left y)) = Left (Right y)
        f (Right (Right z)) = Right z
    alt x y = Alt x y

    cut Nil _ = Nil
    cut _ Nil = Nil
    cut (Not Nil) x = FMap ((),) x
    cut x (Not Nil) = FMap (,()) x
    cut (Eps x) y = maybe Nil (Eps . (x,)) (n' y)
    -- cut (Eps x) y = FMap (x,) (v y)
    cut x (Eps y) = maybe Nil (Eps . (,y)) (n' x)
    -- cut x (Eps y) = FMap (,y) (v x)
    -- Might need to repeat?
    cut (Cut x y) z = FMap (\(a,(b,c)) -> ((a,b),c)) $ Cut x (Cut y z)
    cut x y = Cut x y
    -- Cut Sym Sym would be useful.

    seq :: forall a x y . Eq a => Re a x -> Re a y -> Re a (x,y)
    seq (Eps x) y = FMap (x,) y
    seq x (Eps y) = FMap (,y) x
    seq Nil _ = Nil
    seq _ Nil = Nil
    -- Dubious..
    seq x (Rep y) | compareStructure x y = maybe (Seq x) (FMap . (,)) (n' x) (Rep y)
    -- Might need to repeat?
    seq (Seq x y) z = FMap (\(a,(b,c)) -> ((a,b),c) ) $ Seq x (Seq y z)
    seq x y = Seq x y

    rep Nil = Eps []
    -- We've got a choice here.
    rep (Eps _) = Eps []
    -- Rep (Eps x) = Eps [x,..]
    -- We've got a choice here!
    rep (Rep a) = FMap (:[]) $ Rep a
    -- rep (Rep a) = Rep $ FMap (:[]) a
    -- This would be valid, if we weren't parsing:
    -- rep (Sym Nothing) = Rep $ Not $ Nil
    rep x = Rep x

    -- -- TODO: Figure out the type magic here.
    -- This can be pretty inefficient.
    -- Seq (Rep a) (Rep b) | _ a == b -> FMap (const ([],[])) $ Rep a
    -- Seq (Rep a) (Rep b) -> FMap (const ([],[])) $ Rep a
    not (Not x) = FMap (const ()) x
    not x = Not x
    -- catch all:
    eps x = Eps x

    nil = Nil

    fm f (FMap g x) = FMap (f . g) x
    fm f x = FMap f x

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

prop_float_noincrease :: Re Char String -> Bool
prop_float_noincrease re = size (floatFMap re) <= size re

prop_match_noincrease :: Re Char String -> String -> Property
prop_match_noincrease re s = counterexample (unlines $ "REs:" : map show matches) $
    descending $ map size $ matches where
    descending l = l == reverse (sort l)
    matches = matchn re s

prop_match_noStarIncrease :: Re Char String -> String -> Property
prop_match_noStarIncrease re s = counterexample (unlines $ "REs:" : map show matches) $
    descending $ map starHeight $ matches where
    descending l = l == reverse (sort l)
    matches = matchn re s

prop_match_no_overstar :: Re Char String -> String -> Property
prop_match_no_overstar re s = counterexample (unlines $ ("REs : " ++ show maxStar): map show matches) $
    all (\re' -> maxStar >= size re') $ matches where
    matches = matchn re s
    maxStar = maxStarSize re

-- This grows like crazy.
-- $(!((.*)(([]|ε)(.+)*)|(.*)*))
-- "\138\239\173\183\t\221_{4\211,\178\&3]dI\SI\US\vC\248@\DC3?1"

return []
-- runTests = $verboseCheckAll
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
