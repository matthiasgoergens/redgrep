{-# LANGUAGE GADTs,StandaloneDeriving,TupleSections #-}
import Data.List

-- Add character classes later.
data Re a x where
    Sym :: Maybe [a] -> Re a a
    Alt :: Re a x -> Re a y -> Re a (Either x y)
    Cut :: Re a x -> Re a y -> Re a (x,y)
    Seq :: Re a x -> Re a y -> Re a (x,y)
    Rep :: Re a x -> Re a [x]
    Not :: Re a x -> Re a ()
    Eps :: Re a ()
    Nil :: Re a x
    FMap :: (x -> y) -> Re a x -> Re a y

-- deriving instance Show (ReX a x)
-- deriving instance Eq (ReX a x)
-- deriving instance Ord (ReX a x)

show' :: Re Char x -> String
show' re = case re of
    Sym Nothing -> "."
    Sym (Just [x]) -> x:[]
    Sym (Just xs) -> "[" ++ concatMap show xs ++ "]"
    Alt a b -> show' a ++ "|" ++ show' b
    Cut a b -> show' a ++ "&" ++ show' b
    Seq a b -> show' a ++ show' b
    Rep a -> show' a ++ "*"
    Not a -> "!" ++ show' a
    Eps -> "ε"
    Nil -> "∅"

-- nullable?
v :: Re b x -> Re b ()
v a = if n a then Eps else Nil

n :: Re a x -> Bool
n (Sym _) = False
n (Alt a b) = n a || n b
n (Cut a b) = n a && n b
n (Seq a b) = n a && n b
n (Rep _) = True
n (Not a) = not (n a) -- not convinced.
n Eps = True
n Nil = False

-- simplify1 :: Eq a => Re a x -> Re a x
simplify1 re = case re of
    Alt Nil x -> FMap Right x
    Alt x Nil -> FMap Left x
    Cut Nil x -> Nil
    Cut x Nil -> Nil
    Cut (Not Nil) x -> FMap ((),) x
    Cut x (Not Nil) -> FMap (,()) x
    Seq Eps x -> FMap ((),) x
    Seq x Eps -> FMap (,()) x
    Seq Nil x -> Nil
    Seq x Nil -> Nil
    Rep Nil -> FMap (const []) Eps
    Rep Eps -> FMap (:[]) Eps
    -- We've got a choice here!
    Rep (Rep a) -> FMap (:[]) $ Rep a
    -- Rep (Rep a) -> Rep $ FMap (:[]) a

    -- -- TODO: Figure out the type magic here.
    -- This can be pretty inefficient.
    -- Seq (Rep a) (Rep b) | _ a == b -> FMap (const ([],[])) $ Rep a
    -- Seq (Rep a) (Rep b) -> FMap (const ([],[])) $ Rep a
    Not (Not x) -> FMap (const ()) x
    -- catch all:
    x -> x
simplify = foldRe1 simplify1

-- type C2 a = Re a x -> Re a -> Re a
-- type C1 a = Re a -> Re a
-- foldRe1 :: C1 a -> C1 a 
-- -- Needs more typing magic!
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

-- d :: Eq a => a -> Re a -> Re a
d c (Sym Nothing) = Eps
d c (Sym (Just as))
    | c `elem` as = Eps
    | otherwise = Nil
d c (Alt a b) = Alt (d c a) (d c b)
d c (Cut a b) = Cut (d c a) (d c b)
d c (Seq a b) = Seq (d c a) b `Alt` Seq (v a) (d c b)
d c (Rep a) = Seq (d c a) (Rep a)
d c (Not a) = Not (d c a) -- Not convinced of this, yet.
d _ Eps = Nil
d _ Nil = Nil

ds c = simplify . d c

-- flapping' :: Re Char
flapping' = simplify $ Cut
    (Not $ dots `Seq` str "flapping" `Seq` dots)
    (dots `Seq` str "ping" `Seq` dots)

-- flapping :: Re Char
-- flapping' = not (dots . "flap") . ping . dots
flapping = seqs [Not $ dots `Seq` str "flap"
                , str "ping", dots]

opts r = Alt Eps r
seqs = foldr Seq Eps

-- match :: Eq a => Re a -> [a] -> Bool
match re s = n $ foldl (flip d) re s

matchn re s = scanl (flip ds) re s
-- sym :: [a] -> Re a
sym = Sym . return

-- str :: [a] -> Re a
str = foldr Seq Eps . map (Sym . Just . (:[]))

dots = Rep (Sym Nothing)
dot = Sym Nothing
pp = putStrLn . show'

main = do
    print $ match (sym "a") "a"
    print $ match (Rep (sym "a")) "aaaaaba"
    mapM pp $ matchn (Rep (sym "a")) "aaaaaba"
    putStrLn ""
    mapM pp $ matchn dots "aaaaaba"
    putStrLn "---"
    let s = "xflappinge ping blub"
    mapM pp $ matchn flapping s
    print $ match flapping s

    -- print $ match (Not (str "flapping")) "flapping"
    -- print $ match (dots `Seq` (Not $ str "flapping")) "flapping"
