{-# LANGUAGE FlexibleInstances #-}
import Control.Applicative
import Prelude hiding (seq, not)
import qualified Prelude as P
import qualified Types as T
import Util
import Data.List

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
-- s = success
-- f = failure
class Ini r where
    ini :: r s f

class Sym r where
    sym :: Range -> r Char SymE
class Alt r where
    alt :: r s f -> r s' f' -> r (AltI s s') (CutI f f')
class Cut r where
    cut :: r s f -> r s' f' -> r (CutI s s') (AltI f f')
class Seq r where
    seq :: r s f -> r s' f' -> r (SeqI s s') (AltI f (SeqI s f'))
class Rep r where
    rep :: r s f -> r (RepI s) (SeqI (RepI s) f)
class Not r where
    not :: r s f -> r f s
class Eps r where
    eps :: s -> r s ()
class Nil r where
    nil :: f -> r s f

bifun :: (s -> s') -> (f -> f') -> Backtrack x y s f -> Backtrack x y s' f'
bifun g h (Backtrack b) = Backtrack $ \s f ->
    b (s . g) (f . h)

newtype Backtrack x y s f = Backtrack ((s -> String -> Either x y) -> (f -> String -> Either x y) -> String -> Either x y)

-- or last Left
firstRight :: Either a b -> [Either a b] -> Either a b
firstRight a l = foldr1 (+++) (a : l) where


r@(Right _) +++ _ = r
_ +++ b = b

-- Need to swap all arguments, to make the functor work on the Right result.
-- instead of error.
instance Functor (Backtrack x y s) where
    fmap f = bifun id f
instance Sym (Backtrack x y) where
    sym range = Backtrack $ \s f str ->
        firstRight (f Before str) $
        case str of
            [] -> []
            (x:xs) -> (case rangeMatch range x of
                Just x -> s x xs
                Nothing -> f (Wrong x range) xs) : map (f TooMany) (tails xs)
instance Seq (Backtrack x y) where
    seq (Backtrack x) (Backtrack y) = Backtrack $ \scont fcont ->
        let sx s_ = y (scont . Seq s_) (fcont . AltR . Seq s_)
            fx ff = fcont $ AltL ff
        in x sx fx

instance Alt (Backtrack x y) where
    alt (Backtrack x) (Backtrack y) = Backtrack $ \scont fcont str ->
        x (scont . AltL)
          (\err _ -> y (scont . AltR) (fcont . Cut err) str)
          str
instance Rep (Backtrack x y) where
    rep x = bifun sf ff $ alt (eps $ Rep []) (seq x $ rep x) where
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

instance Not (Backtrack x y) where
    not (Backtrack f) = Backtrack $ flip f
instance Eps (Backtrack x y) where
--        firstRight (f Before str) $
    eps orig = Backtrack $ \scont fcont str ->
        scont orig str +++ fcont () str
        
evalB :: Backtrack (Maybe f) s s f -> String -> Either (Maybe f) s
evalB (Backtrack fn) = fn succ fail where
    succ val [] = Right val
    succ _ _ = Left Nothing
    fail err [] = Left (Just err)
    fail _ _ = Left Nothing


c :: (Sym r) => Char -> r Char SymE
c x = sym . pure . pure $ x
xh :: Sym r => r Char SymE
xh = sym (Just "xh")

hello :: (Sym r, Seq r) => r (SeqI Char Char) (AltI SymE (SeqI Char SymE))
hello = c 'h' `seq` c 'e'

hello2 :: (Sym r, Seq r, Not r) => r (SeqI SymE Char) (AltI Char (SeqI SymE SymE))
hello2 = not (c 'h') `seq` c 'e'

hello3 :: (Rep r, Sym r, Seq r, Not r) => r (SeqI Char (RepI Char)) (AltI SymE (SeqI Char (SeqI (RepI Char) SymE)))
hello3 = (c 'h') `seq` rep (c 'e')

-- optional :: (Alt r, Eps r) => r (AltI () Char) (CutI 

main = do
    print $ evalB (sym (Just "xh")) "xhello"
    print $ evalB hello "he"
    print $ evalB hello "xx"
    print $ evalB hello2 "xe"
    print $ evalB hello3 "heeex"
    print $ evalB hello3 "heeee"
    print $ evalB (sym Nothing) "a"
    print $ evalB (rep (sym Nothing)) "aaaa"
    print $ evalB (eps ('a' :: Char) `alt` c 'x') ""


