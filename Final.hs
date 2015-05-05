{-# LANGUAGE FlexibleInstances #-}
import Control.Applicative
import Prelude hiding (seq)
import qualified Types as T
import Util
import Data.List

data SymE = Before | Wrong | TooMany
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
    eps :: s -> r s f
class Nil r where
    nil :: f -> r s f

bifun :: (s -> s') -> (f -> f') -> Backtrack x y s f -> Backtrack x y s' f'
bifun g h (Backtrack b) = Backtrack $ \s f ->
    b (\s_  -> s $ g s_) (\f_ -> f $ h f_)

newtype Backtrack x y  s f = Backtrack ((s -> String -> Either x y) -> (f -> String -> Either x y) -> String -> Either x y)

-- or last Left
firstRight :: Either a b -> [Either a b] -> Either a b
firstRight a l = foldr1 (+) (a : l) where
    r@(Right _) + _ = r
    _ + b = b

instance Sym (Backtrack x y) where
    sym range = Backtrack $ \s f str ->
        firstRight (f Before []) $
        case str of
            [] -> []
            (x:xs) -> (case rangeMatch range x of
                Just x -> s x xs
                Nothing -> f Wrong xs) : map (f TooMany) (tails xs)
instance Seq (Backtrack x y) where
    seq (Backtrack x) (Backtrack y) = Backtrack $ \scont fcont ->
        let sx s_ = y (scont . Seq s_) (fcont . AltR . Seq s_)
            fx ff = fcont $ AltL ff
        in x sx fx


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

main = do
    print $ evalB (sym (Just "xh")) "xhello"
    print $ evalB (hello) "he"

