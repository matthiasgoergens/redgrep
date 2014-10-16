{-# LANGUAGE GADTs,TupleSections #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FlexibleContexts #-}
import Data.Typeable
import Control.Applicative
import Test.QuickCheck
-- import Data.Either.Combinators


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
instance Arbitrary (Re Char Char) where
    arbitrary = Sym <$> arbitrary
    shrink (Sym s) = Sym <$> shrink s
    shrink _ = []

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
        FMap _ a -> show a -- Not great.

-- Something wrong here.
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

v' :: Re a x -> Re a x
v' = maybe Nil Eps . n'

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


simplify,s :: Eq a => Re a x -> Re a x
s = simplify
-- Lenses or boilerplate scrapping?
simplify re = case re of
    Alt Nil x -> FMap Right (s x)
    Alt x Nil -> FMap Left (s x)
    Cut Nil _ -> Nil
    Cut _ Nil -> Nil
    Cut (Not Nil) x -> FMap ((),) (s x)
    Cut x (Not Nil) -> FMap (,()) (s x)
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

d :: Eq a => a -> Re a x -> Re a x
d c (Sym Nothing) = Eps c
d c (Sym (Just as))
    | c `elem` as = Eps c
    | otherwise = Nil
d c (Alt a b) = Alt (d c a) (d c b)
d c (Cut a b) = Cut (d c a) (d c b)
d c (Seq a b) = FMap (either id id) $ Seq (d c a) b `Alt` Seq (v' a) (d c b)
d c (Rep a) = FMap (uncurry (:)) $ Seq (d c a) (Rep a)
d c (Not a) = Not (d c a)
d _ (Eps _) = Nil
d _ Nil = Nil
d c (FMap f x) = FMap f (d c x)

-- Pass to float up FMaps? --- especially needed for minimization.

instance Functor (Re a) where
    -- We could do something more clever, by recursing.
    fmap = FMap

-- Ha, this is almost trivial!
instance Applicative (Re a) where
    pure = Eps 
    f <*> a = FMap (uncurry ($)) $ Seq f a
instance Alternative (Re a) where
    a <|> b = FMap (either id id) $ Alt a b
    empty = Nil

ds :: Eq a => a -> Re a x -> Re a x
ds c = simplify . d c

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
-- This runs forever.  Bad.
match re = n . foldl (flip ds) re
matchn :: Eq a => Re a x -> [a] -> [Re a x]
matchn   = scanl (flip ds)
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

main :: IO ()
main = do
    print $ match (sym "a") "a"
    print $ match (Rep (sym "a")) "aaaaaba"
    mapM_ pp $ matchn (Rep (sym "a")) "aaaaaba"
    putStrLn ""
    mapM_ pp $ matchn dots "aaaaaba"
    putStrLn "---"
    let s = "xflappinge ping blub"
    mapM_ pp $ matchn flapping s
    print "match:"
    print $ match flapping s
    print "/match"

    -- print $ match (Not (str "flapping")) "flapping"
    -- print $ match (dots `Seq` (Not $ str "flapping")) "flapping"
