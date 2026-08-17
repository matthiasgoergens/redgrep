-- Probe: which random regexes make `compile 500` explode?
module Main (main) where

import Control.Monad (forM_, replicateM)
import System.Timeout (timeout)
import Test.QuickCheck
import Test.QuickCheck.Gen (unGen)
import Test.QuickCheck.Random (mkQCGen)
import qualified Data.Set as Set
import qualified Redgrep.Core as C

gen :: Int -> Gen C.RE
gen n
    | n <= 0 = leaf
    | otherwise = frequency
        [ (2, leaf)
        , (2, C.alt2 <$> sub <*> sub)
        , (1, C.cut2 <$> sub <*> sub)
        , (2, C.seq2 <$> sub <*> sub)
        , (1, C.rep_ <$> gen (n - 1))
        , (1, C.not_ <$> gen (n - 1))
        ]
  where
    sub = gen (n `div` 2)
    leaf = frequency
        [ (3, C.sym . C.Pos . Set.fromList <$> sublistOf "abc")
        , (1, pure C.dot)
        , (1, pure C.Eps)
        , (1, pure C.Nil)
        ]

main :: IO ()
main = forM_ [1 .. 400 :: Int] $ \i -> do
    let r = unGen (gen 5) (mkQCGen i) 30
    res <- timeout 500000 (case C.compile 500 r of
        Nothing -> pure (Left ())
        Just comp -> comp `seq` pure (Right ()))
    case res of
        Nothing -> putStrLn ("SLOW seed " ++ show i ++ ": size " ++ show (C.size r) ++ "  " ++ show r)
        Just _ -> pure ()
