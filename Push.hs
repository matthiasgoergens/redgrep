{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
import Final hiding (main)
import Control.Applicative
import Control.Monad
import Prelude hiding (seq, not)
import qualified Prelude as P
import qualified Types as T
import Util
import Data.List
import Data.String
import Data.Biapplicative
import Data.Bifunctor  
-- that's almost the state monad?
-- But, this doesn't allow us to _unify_ two strands!
-- We need more internal structure for that. (Or don't we, because when we implement,
-- we can look into the internal structure?)
data Push f s = Push { now :: Either f s
                     , next :: Char -> Push f s
                     }
-- I think we can introduce IDs for union-ing non-deterministic choice  
-- and use the type system to help us only compare like with like.
-- in Push, the (->) hides all the state.
evalP :: Push f s -> String -> Either f s
evalP push str = now $ foldl next push str
instance Nil Push where
    nil = let me = Push { now = Left (), next = const me } in me
instance Eps Push where
    eps = Push { now = Right (), next = const $ nil }
instance Not Push where
    not a = Push { now = switch $ now a
                 , next = not . next a
                 }
instance Bifun Push where
    bifun h g = not . fmap h . not . fmap g
instance Functor (Push f) where
    fmap g a = Push { now = fmap g $ now a
                    , next = fmap g . next a
                    }
instance Sym Push where
    sym range = Push
        { now = Left Before
        , next = \x ->
            case rangeMatch range x of
                Just x -> eps_ TooMany x
                Nothing -> nil_ $ Wrong range x
        }
-- We need to be able to tag with history, and unify.
-- Seq Push has the full convolution.
instance Seq Push where 
    seq a b = Push 
        { now = case (now a, now b) of 
            (Right a, Right b) -> Right (Seq a b) 
            (Left a, _) -> Left (AltL a) 
            (Right a, Left b) -> Left (AltR (Seq a b)) 
        , next =  
            let b' = case now a of 
                        Left a -> const (nil_ (AltL a)) b 
                        Right a -> bifun (AltR . Seq a) (Seq a) $ b 
                fail (Cut a b) = a 
                succ (AltL a) = a
                succ (AltR b) = b
            in \char -> bifun fail succ $
                        (next a char `seq` b) `alt`
                        next b' char
        }
instance Alt Push where
    alt a b = Push
        { now = case (now a, now b) of
            (Left a, Left b) -> Left $ Cut a b
            -- Left biased.
            (Right a, _) -> Right $ AltL a
            (Left _, Right b) -> Right (AltR b)
        , next = \char -> next a char `alt` next b char
        }

instance IsString (Push () String) where
    fromString = string

main = do
    r $ print $ evalP hello2 "xe"
    let text :: Push () String
        text = "hellox"
    r $ print $ evalP text "hellox"
