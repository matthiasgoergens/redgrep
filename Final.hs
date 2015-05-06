{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Control.Applicative
import Prelude hiding (seq, not)
import qualified Prelude as P
import qualified Types as T
import Util
import Data.List
import Data.String

data SymE = Before | Wrong Char Range | TooMany
    deriving (Eq, Ord, Show)
data AltI a b = AltL a | AltR b | AltB a b
    deriving (Eq, Ord, Show)
data CutI a b = Cut a b
    deriving (Eq, Ord, Show)
data SeqI a b = Seq a b
    deriving (Eq, Ord, Show)
data RepI a = Rep [a]
    deriving (Eq, Ord, Show)

type Range = Maybe [Char]

-- r = representation
-- f = failure
-- s = success
class Ini r where
    ini :: r f s

class Sym r where
    sym :: Range -> r SymE Char
class Alt r where
    alt :: r f s -> r f' s' -> r (CutI f f') (AltI s s')
class Cut r where
    cut :: r f s -> r f' s' -> r (AltI f f') (CutI s s')
class Seq r where
    seq :: r f s -> r f' s' -> r (AltI f (SeqI s f')) (SeqI s s') 
class Rep r where
    rep :: r f s -> r (SeqI (RepI s) f) (RepI s)
class Not r where
    not :: r s f -> r f s
class Eps r where
    eps :: f -> s -> r f s
class Nil r where
    nil :: f -> r f s

-- bifun :: (f -> f') -> (s -> s') -> Backtrack y x f s -> Backtrack y x f' s'
bifun h g = not . fmap h . not . fmap g

instance IsString (Backtrack y x () String) where
    fromString = string

string ::
    String -> Backtrack y x () String
string s = foldr h (eps () []) s where
    h char r = bifun fail succ $ seq (c char) r
    succ (Seq c r) = c : r
    -- TODO: figure out good error reporting
    fail (AltL l) = ()
    fail (AltR r) = ()
    fail (AltB l r) = ()

newtype Backtrack y x f s = Backtrack ((f -> String -> Either y x) -> (s -> String -> Either y x) -> String -> Either y x)

-- or last Left
firstRight :: Either a b -> [Either a b] -> Either a b
firstRight a l = foldr1 (+++) (a : l) where


r@(Right _) +++ _ = r
_ +++ b = b

-- Need to swap all arguments, to make the functor work on the Right result.
-- instead of error.
instance Functor (Backtrack y x f) where
    fmap g (Backtrack b) = Backtrack $ \fail succ ->
        b fail (succ . g)

-- The failure branch is a bit iffy.
instance Monoid f => Applicative (Backtrack y x f) where
    pure x = eps mempty x
    fn <*> res = bifun fail (\(Seq f a) -> f a) $ fn `seq` res where
        fail (AltL f) = f
        fail (AltR (Seq _ f)) = f
        fail (AltB fa (Seq _ fb)) = fa `mappend` fb

instance Sym (Backtrack y x) where
    sym range = Backtrack $ \f s str ->
        firstRight (f Before str) $
        case str of
            [] -> []
            (x:xs) -> (case rangeMatch range x of
                Just x -> s x xs
                Nothing -> f (Wrong x range) xs) : map (f TooMany) (tails xs)
instance Seq (Backtrack y x) where
    seq (Backtrack x) (Backtrack y) = Backtrack $ \fcont scont ->
        let sx s_ = y (fcont . AltR . Seq s_) (scont . Seq s_)
            fx ff = fcont $ AltL ff
        in x fx sx
cutD x y = not $ alt (not x) (not y)
instance Cut (Backtrack x y) where
    -- de morgan
    -- cut x y = not $ alt (not x) (not y)
    -- This is wrong.  We'd need to check whether both match at the same time.
    cut (Backtrack x) (Backtrack y) = Backtrack $ \fcont scont str ->
        x (fcont . AltL)
          (\val _ -> y (fcont . AltR) (scont . Cut val) str)
          str
instance Alt (Backtrack y x) where
    alt (Backtrack x) (Backtrack y) = Backtrack $ \fcont scont str ->
        x (\err _ -> y (fcont . Cut err) (scont . AltR) str)
          (scont . AltL)
          str
instance Rep (Backtrack y x) where
    rep x = bifun ff sf $ alt (eps () (Rep [])) (seq x $ rep x) where
        sf (AltL r) = r
        sf (AltR (Seq a (Rep b))) = Rep (a:b)
        sf (AltB r _) = r
        ff (Cut _ r) = case r of
            AltL f -> Seq (Rep []) f
            AltR (Seq x (Seq (Rep xs) f)) -> Seq (Rep $ x:xs) f
            AltB f _ -> Seq (Rep []) f
-- CutI f0
--      (AltI f
--            (SeqI s (SeqI (RepI s) f)))
-- -> SeqI (RepI s) f

switch :: Either a b -> Either b a
switch (Left a) = Right a
switch (Right b) = Left b

instance Not (Backtrack y x) where
    not (Backtrack f) = Backtrack $ flip f
instance Eps (Backtrack y x) where
--        firstRight (f Before str) $
    eps err val = Backtrack $ \fcont scont str ->
        scont val str +++ fcont err str
        
evalB :: Backtrack (Maybe f) s f s -> String -> Either (Maybe f) s
evalB (Backtrack fn) = fn fail succ where
    succ val [] = Right val
    succ _ _ = Left Nothing
    fail err [] = Left (Just err)
    fail _ _ = Left Nothing


c :: (Sym r) => Char -> r SymE Char
c x = sym . pure . pure $ x
xh :: Sym r => r SymE Char
xh = sym (Just "xh")

hello :: (Sym r, Seq r) => r (AltI SymE (SeqI Char SymE)) (SeqI Char Char)
hello = c 'h' `seq` c 'e'

hello2 :: (Sym r, Seq r, Not r) => r (AltI Char (SeqI SymE SymE)) (SeqI SymE Char)
hello2 = not (c 'h') `seq` c 'e'

hello3 :: (Sym r, Seq r, Rep r) =>
    r (AltI SymE (SeqI Char (SeqI (RepI Char) SymE)))
      (SeqI Char (RepI Char))
hello3 = (c 'h') `seq` rep (c 'e')


-- optional :: (Alt r, Eps r) => r (AltI () Char) (CutI 

r b = putStr "R " >> b
l b = putStr "L " >> b

xTest = rep "hello world "


main = do
    print $ evalB (sym (Just "xh")) "xhello"
    print $ evalB hello "he"
    print $ evalB hello "xx"
    print $ evalB hello2 "xe"
    print $ evalB hello3 "heeex"
    print $ evalB hello3 "heeee"
    r $ print $ evalB (sym Nothing) "a"
    r $ print $ evalB (rep (sym Nothing)) "aaaa"
    r $ print $ evalB (eps 12 () `alt` c 'x') ""
    let s = string
    r $ print $ evalB (seq ((s "a" `seq` rep (s "ba")) `cut`
                           (rep (s "ab") `seq` (s "a")))
                        $ c 'x')
                    "ababax"
    r $ print $ evalB (seq ((s "a" `seq` rep (s "ba")) `cutD`
                           (rep (s "ab") `seq` (s "a")))
                        $ c 'x')
                    "ababax"


